-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:41:18.503362+00:00
-- url     : https://prove2.me/submissions/70f43bcd-c994-432b-ae2b-8d66dedc725f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E124
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound0_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound100_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound101_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound102_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound103_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound104_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound105_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound106_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound107_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound108_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound109_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound110_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound111_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound112_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound113_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound114_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound115_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound116_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound117_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound118_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound119_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound11_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound120_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound121_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound122_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound123_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound124_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound125_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound126_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound127_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound128_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound129_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound12_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound130_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound131_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound132_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound133_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound134_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound135_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound136_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound137_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound138_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound139_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound13_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound140_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound141_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound142_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound143_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound144_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound145_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound146_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound147_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound148_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound149_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound14_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound150_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound151_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound15_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound16_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound17_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound18_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound19_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound1_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound20_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound21_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound23_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound24_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound25_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound26_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound27_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound28_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound29_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound2_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound30_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound31_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound32_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound33_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound34_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound35_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound36_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound37_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound38_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound39_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound3_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound40_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound41_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound42_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound43_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound44_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound45_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound46_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound47_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound48_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound49_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound4_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound50_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound51_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound52_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound53_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound54_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound55_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound56_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound57_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound58_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound59_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound5_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound60_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound61_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound62_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound63_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound64_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound65_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound66_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound67_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound68_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound69_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound6_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound70_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound71_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound72_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound73_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound74_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound75_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound76_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound77_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound78_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound79_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound7_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound80_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound81_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound82_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound83_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound84_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound85_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound86_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound87_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound88_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound89_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound8_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound90_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound91_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound92_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound93_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound94_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound95_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound96_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound97_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound98_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound99_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_chunkSound9_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound163_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound353_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound354_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound355_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound356_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound357_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound358_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound359_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound365_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound366_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound367_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

theorem g_difference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (difference i j) = if i = j then 1 else 0 := by
  simp only [g, character_difference _ (fun k => hH.1 k _)]
  rw [hH.row_orthogonal]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_ChargeDecomposition
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem weightMultiset_card (w : Coord → ℕ) :
    (weightMultiset w).card = ∑ i, w i := by
  have h (s : Finset Coord) : (∑ i ∈ s, Multiset.replicate (w i) i).card = ∑ i ∈ s, w i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.card_add, ih]
  exact h Finset.univ

theorem weightMultiset_count (w : Coord → ℕ) (k : Coord) :
    (weightMultiset w).count k = w k := by
  have h (s : Finset Coord) :
      (∑ i ∈ s, Multiset.replicate (w i) i).count k = ∑ i ∈ s, if i = k then w i else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.count_add, Multiset.count_replicate, ih]
  simpa [weightMultiset] using h Finset.univ

theorem positivePositions_card (a : Charge) : (positivePositions a).card = order a :=
  weightMultiset_card _

theorem negativePositions_card {a : Charge} (ha : Balanced a) :
    (negativePositions a).card = order a := by
  have h : (∑ i, ((a i).toNat : ℤ)) - ∑ i, ((-a i).toNat : ℤ) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using (show ∑ i, a i = 0 from ha)
  rw [negativePositions, weightMultiset_card, order]
  exact_mod_cast (sub_eq_zero.mp h).symm

theorem charge_eq_counts (a : Charge) (k : Coord) :
    a k = ((positivePositions a).count k : ℤ) - (negativePositions a).count k := by
  rw [positivePositions, negativePositions, weightMultiset_count, weightMultiset_count]
  exact (Int.toNat_sub_toNat_neg _).symm

theorem positive_negative_ne {a : Charge} {i j : Coord}
    (hi : i ∈ positivePositions a) (hj : j ∈ negativePositions a) : i ≠ j := by
  intro h
  subst j
  rw [← Multiset.count_pos, positivePositions, weightMultiset_count] at hi
  rw [← Multiset.count_pos, negativePositions, weightMultiset_count] at hj
  have hp := Int.pos_iff_toNat_pos.mpr hi
  have hn := Int.pos_iff_toNat_pos.mpr hj
  omega

/-- A balanced charge of order one is one positive and one negative coordinate. -/
theorem order_one_decomposition {a : Charge} (ha : Balanced a) (ho : order a = 1) :
    ∃ i j, i ≠ j ∧ a = difference i j := by
  obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp ((positivePositions_card a).trans ho)
  obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp ((negativePositions_card ha).trans ho)
  refine ⟨i, j, positive_negative_ne (a := a) (by simp [hi]) (by simp [hj]), ?_⟩
  funext k
  rw [charge_eq_counts a k, hi, hj]
  simp [difference, Pi.single_apply, Multiset.count_singleton, eq_comm]

theorem g_order_one {H : CMatrix} (hH : IsHadamard H) {a : Charge}
    (ha : Balanced a) (ho : order a = 1) : g H a = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := order_one_decomposition ha ho
  simp [g_difference hH, hij]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem embedCharge_sum {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    ∑ i, embedCharge ρ a i = ∑ i, a i := by
  symm
  exact Fintype.sum_of_injective ρ ρ.injective a (embedCharge ρ a)
    (embedCharge_outside ρ a) (fun i => (embedCharge_apply ρ a i).symm)

theorem embedCharge_order {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    order (embedCharge ρ a) = ∑ i, (a i).toNat := by
  symm
  apply Fintype.sum_of_injective ρ ρ.injective (fun i => (a i).toNat)
    (fun i => (embedCharge ρ a i).toNat)
  · intro i hi
    rw [embedCharge_outside ρ a i hi]
    rfl
  · intro i
    rw [embedCharge_apply]

theorem embedCharge_neg {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    embedCharge ρ (-a) = -embedCharge ρ a := by
  funext i
  by_cases hi : i ∈ Set.range ρ
  · obtain ⟨j, rfl⟩ := hi
    simp
  · simp [Pi.neg_apply, embedCharge_outside ρ _ i hi]

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_neg {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ (-a) = conj (rowFourier H ρ a) := by
  rw [rowFourier_eq_g, embedCharge_neg, g_neg hH, rowFourier_eq_g]

theorem rowFourier_order_one {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (ha : ∑ i, a i = 0)
    (ho : ∑ i, (a i).toNat = 1) : rowFourier H ρ a = 0 := by
  rw [rowFourier_eq_g]
  apply g_order_one hH
  · exact (embedCharge_sum ρ a).trans ha
  · exact (embedCharge_order ρ a).trans ho

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_neg {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B (-A) label = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  have h : mixedIntegrand B (-A) label r ρ τ = conj (mixedIntegrand B A label r ρ τ) := by
    unfold mixedIntegrand
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_neg (relativeMatrix_isHadamard B hB r _) ρ _
  rw [h, Complex.conj_re]

theorem mixedMoment_factor_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B (fun i j => A i (σ j)) (label ∘ σ) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  exact congrArg Complex.re (Equiv.prod_comp σ
    (fun j => rowFourier (relativeMatrix B r (τ (label j))) ρ (fun i => A i j)))

theorem rowFourier_row_permutation {p : ℕ} (H : CMatrix) (a : Fin p → ℤ)
    (σ : Equiv.Perm (Fin p)) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ (a ∘ σ) =
      rowFourier H (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) a := by
  unfold rowFourier
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => H (ρ (σ.symm i)) k ^ a i)

theorem mixedMoment_row_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin p)) :
    mixedMoment B (fun i j => A (σ i) j) label = mixedMoment B A label := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B (fun i j => A (σ i) j) label r ρ τ =
        mixedIntegrand B A label r (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_row_permutation _ (fun i => A i j) σ ρ
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B A label r ρ τ).re))

theorem mixedMoment_order_one {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (ha : ∑ i, A i j = 0) (ho : ∑ i, (A i j).toNat = 1) : mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact rowFourier_order_one (relativeMatrix_isHadamard B hB r _) ρ _ ha ho
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowFourier_zero_first {p : ℕ} (H : CMatrix) (a : Fin (p + 1) → ℤ)
    (ha : a 0 = 0) (ρ : Fin (p + 1) ↪ Coord) :
    rowFourier H ρ a = rowFourier H (Sampling.dropFirst ρ) (fun i => a i.succ) := by
  simp only [rowFourier, Fin.prod_univ_succ, ha, zpow_zero, one_mul]
  rfl

theorem mixedMoment_zero_first_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (hA : ∀ j, A 0 j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i.succ j) label := by
  apply average_congr
  intro r
  have h (ρ : Fin (p + 1) ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ =
        mixedIntegrand B (fun i j => A i.succ j) label r (Sampling.dropFirst ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_zero_first _ (fun i => A i j) (hA j) ρ
  simp_rw [h]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B (fun i j => A i.succ j) label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedShifts
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sampledMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s : Coord) : IsHadamard (sampledMatrix B r ρ s) := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  exact (relativeMatrix_isHadamard B hB r s).permutations e (Equiv.refl Coord)

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Rules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sound rules for mixed certificate normalization

Generated witnesses may only permute rows or factors, negate all charges,
remove zero rows or factors, and injectively rename labels. The equalities
here justify those operations for the actual finite mixed moments.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem permute {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i) (σ j)) (label ∘ σ) := by
  rw [mixedMoment_factor_permutation B (fun i j => A (ρ i) j) label σ,
    mixedMoment_row_permutation]

theorem delete_zero_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin (p + 1))) (hz : ∀ j, A (ρ 0) j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i.succ) j) label := by
  rw [← mixedMoment_row_permutation B A label ρ]
  exact mixedMoment_zero_first_row hp B _ label hz

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5308 raw5308Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5308 raw5308Labels = mixedMoment B raw5308step0 raw5308step0Labels := by
      have hz : ∀ j, raw5308 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5308step0 = (fun i j => raw5308 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5308step0 raw5308; decide +kernel
      have hl : raw5308step0Labels = raw5308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5308 raw5308Labels permutation265 hz
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical5311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5311 raw5311Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5311 raw5311Labels = mixedMoment B raw5311step0 raw5311step0Labels := by
      have hz : ∀ j, raw5311 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5311step0 = (fun i j => raw5311 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5311step0 raw5311; decide +kernel
      have hl : raw5311step0Labels = raw5311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5311 raw5311Labels permutation265 hz
    mixedMoment B raw5311step0 raw5311step0Labels = mixedMoment B raw5311step1 raw5311step1Labels := by
      have ha : raw5311step1 = (fun i j => raw5311step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5311step1 raw5311step0; decide +kernel
      have hl : raw5311step1Labels = raw5311step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5311step0 raw5311step0Labels permutation88 permutation4
    mixedMoment B raw5311step1 raw5311step1Labels = mixedMoment B raw5311step2 raw5311step2Labels := by
      have ha : raw5311step2 = -raw5311step1 := by apply Matrix.ext; change ∀ i j, raw5311step2 i j = -(raw5311step1 i j); unfold raw5311step2 raw5311step1; decide +kernel
      have hl : raw5311step2Labels = raw5311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical5314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5314 raw5314Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5314 raw5314Labels = mixedMoment B raw5314step0 raw5314step0Labels := by
      have hz : ∀ j, raw5314 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5314step0 = (fun i j => raw5314 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5314step0 raw5314; decide +kernel
      have hl : raw5314step0Labels = raw5314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314 raw5314Labels permutation590 hz
    mixedMoment B raw5314step0 raw5314step0Labels = mixedMoment B raw5314step1 raw5314step1Labels := by
      have hz : ∀ j, raw5314step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw5314step1 = (fun i j => raw5314step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw5314step1 raw5314step0; decide +kernel
      have hl : raw5314step1Labels = raw5314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314step0 raw5314step0Labels permutation128 hz
    mixedMoment B raw5314step1 raw5314step1Labels = mixedMoment B raw5314step2 raw5314step2Labels := by
      have hz : ∀ j, raw5314step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5314step2 = (fun i j => raw5314step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5314step2 raw5314step1; decide +kernel
      have hl : raw5314step2Labels = raw5314step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314step1 raw5314step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5317 raw5317Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw5317 raw5317Labels = mixedMoment B raw5317step0 raw5317step0Labels := by
      have hz : ∀ j, raw5317 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5317step0 = (fun i j => raw5317 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5317step0 raw5317; decide +kernel
      have hl : raw5317step0Labels = raw5317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5317 raw5317Labels permutation265 hz
    mixedMoment B raw5317step0 raw5317step0Labels = mixedMoment B raw5317step1 raw5317step1Labels := by
      have ha : raw5317step1 = (fun i j => raw5317step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5317step1 raw5317step0; decide +kernel
      have hl : raw5317step1Labels = raw5317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5317step0 raw5317step0Labels permutation34 permutation2
    _ = mixedMoment B node1042 node1042Labels := by rfl

theorem canonical5318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5318 raw5318Labels = mixedMoment B node1030 node1030Labels := by
  calc
    mixedMoment B raw5318 raw5318Labels = mixedMoment B raw5318step0 raw5318step0Labels := by
      have hz : ∀ j, raw5318 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5318step0 = (fun i j => raw5318 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5318step0 raw5318; decide +kernel
      have hl : raw5318step0Labels = raw5318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5318 raw5318Labels permutation265 hz
    _ = mixedMoment B node1030 node1030Labels := by rfl

theorem canonical5321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5321 raw5321Labels = mixedMoment B node2124 node2124Labels := by
  calc
    mixedMoment B raw5321 raw5321Labels = mixedMoment B raw5321step0 raw5321step0Labels := by
      have ha : raw5321step0 = (fun i j => raw5321 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5321step0 raw5321; decide +kernel
      have hl : raw5321step0Labels = raw5321Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5321 raw5321Labels permutation206 permutation2
    _ = mixedMoment B node2124 node2124Labels := by rfl

theorem canonical5325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5325 raw5325Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5325 raw5325Labels = mixedMoment B raw5325step0 raw5325step0Labels := by
      have ha : raw5325step0 = (fun i j => raw5325 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5325step0 raw5325; decide +kernel
      have hl : raw5325step0Labels = raw5325Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5325 raw5325Labels permutation154 permutation2
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5326 raw5326Labels = mixedMoment B node2014 node2014Labels := by
  calc
    _ = mixedMoment B node2014 node2014Labels := by rfl

theorem canonical5328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5328 raw5328Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw5328 raw5328Labels = mixedMoment B raw5328step0 raw5328step0Labels := by
      have hz : ∀ j, raw5328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5328step0 = (fun i j => raw5328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5328step0 raw5328; decide +kernel
      have hl : raw5328step0Labels = raw5328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5328 raw5328Labels permutation265 hz
    mixedMoment B raw5328step0 raw5328step0Labels = mixedMoment B raw5328step1 raw5328step1Labels := by
      have ha : raw5328step1 = (fun i j => raw5328step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5328step1 raw5328step0; decide +kernel
      have hl : raw5328step1Labels = raw5328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5328step0 raw5328step0Labels permutation40 permutation2
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical5331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5331 raw5331Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw5331 raw5331Labels = mixedMoment B raw5331step0 raw5331step0Labels := by
      have hz : ∀ j, raw5331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5331step0 = (fun i j => raw5331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5331step0 raw5331; decide +kernel
      have hl : raw5331step0Labels = raw5331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5331 raw5331Labels permutation265 hz
    mixedMoment B raw5331step0 raw5331step0Labels = mixedMoment B raw5331step1 raw5331step1Labels := by
      have ha : raw5331step1 = (fun i j => raw5331step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5331step1 raw5331step0; decide +kernel
      have hl : raw5331step1Labels = raw5331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5331step0 raw5331step0Labels permutation34 permutation2
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical5332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5332 raw5332Labels = mixedMoment B node2097 node2097Labels := by
  calc
    mixedMoment B raw5332 raw5332Labels = mixedMoment B raw5332step0 raw5332step0Labels := by
      have hz : ∀ j, raw5332 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5332step0 = (fun i j => raw5332 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5332step0 raw5332; decide +kernel
      have hl : raw5332step0Labels = raw5332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5332 raw5332Labels permutation265 hz
    _ = mixedMoment B node2097 node2097Labels := by rfl

theorem canonical5334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5334 raw5334Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw5334 raw5334Labels = mixedMoment B raw5334step0 raw5334step0Labels := by
      have hz : ∀ j, raw5334 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5334step0 = (fun i j => raw5334 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5334step0 raw5334; decide +kernel
      have hl : raw5334step0Labels = raw5334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5334 raw5334Labels permutation520 hz
    mixedMoment B raw5334step0 raw5334step0Labels = mixedMoment B raw5334step1 raw5334step1Labels := by
      have hz : ∀ j, raw5334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5334step1 = (fun i j => raw5334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5334step1 raw5334step0; decide +kernel
      have hl : raw5334step1Labels = raw5334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5334step0 raw5334step0Labels permutation56 hz
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical5335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5335 raw5335Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5335 raw5335Labels = mixedMoment B raw5335step0 raw5335step0Labels := by
      have hz : ∀ j, raw5335 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5335step0 = (fun i j => raw5335 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5335step0 raw5335; decide +kernel
      have hl : raw5335step0Labels = raw5335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5335 raw5335Labels permutation265 hz
    mixedMoment B raw5335step0 raw5335step0Labels = mixedMoment B raw5335step1 raw5335step1Labels := by
      have ha : raw5335step1 = (fun i j => raw5335step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5335step1 raw5335step0; decide +kernel
      have hl : raw5335step1Labels = raw5335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5335step0 raw5335step0Labels permutation35 permutation2
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical5336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5336 raw5336Labels = mixedMoment B node2126 node2126Labels := by
  calc
    mixedMoment B raw5336 raw5336Labels = mixedMoment B raw5336step0 raw5336step0Labels := by
      have hz : ∀ j, raw5336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5336step0 = (fun i j => raw5336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5336step0 raw5336; decide +kernel
      have hl : raw5336step0Labels = raw5336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5336 raw5336Labels permutation265 hz
    mixedMoment B raw5336step0 raw5336step0Labels = mixedMoment B raw5336step1 raw5336step1Labels := by
      have ha : raw5336step1 = (fun i j => raw5336step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5336step1 raw5336step0; decide +kernel
      have hl : raw5336step1Labels = raw5336step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5336step0 raw5336step0Labels permutation38 permutation2
    _ = mixedMoment B node2126 node2126Labels := by rfl

theorem canonical5337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5337 raw5337Labels = mixedMoment B node2125 node2125Labels := by
  calc
    mixedMoment B raw5337 raw5337Labels = mixedMoment B raw5337step0 raw5337step0Labels := by
      have hz : ∀ j, raw5337 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5337step0 = (fun i j => raw5337 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5337step0 raw5337; decide +kernel
      have hl : raw5337step0Labels = raw5337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5337 raw5337Labels permutation265 hz
    mixedMoment B raw5337step0 raw5337step0Labels = mixedMoment B raw5337step1 raw5337step1Labels := by
      have ha : raw5337step1 = (fun i j => raw5337step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5337step1 raw5337step0; decide +kernel
      have hl : raw5337step1Labels = raw5337step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5337step0 raw5337step0Labels permutation38 permutation2
    _ = mixedMoment B node2125 node2125Labels := by rfl

theorem canonical5338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5338 raw5338Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5338 raw5338Labels = mixedMoment B raw5338step0 raw5338step0Labels := by
      have hz : ∀ j, raw5338 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5338step0 = (fun i j => raw5338 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5338step0 raw5338; decide +kernel
      have hl : raw5338step0Labels = raw5338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5338 raw5338Labels permutation265 hz
    mixedMoment B raw5338step0 raw5338step0Labels = mixedMoment B raw5338step1 raw5338step1Labels := by
      have ha : raw5338step1 = (fun i j => raw5338step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5338step1 raw5338step0; decide +kernel
      have hl : raw5338step1Labels = raw5338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5338step0 raw5338step0Labels permutation33 permutation2
    _ = mixedMoment B node2253 node2253Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5399 raw5399Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5399 raw5399Labels = mixedMoment B raw5399step0 raw5399step0Labels := by
      have hz : ∀ j, raw5399 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5399step0 = (fun i j => raw5399 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5399step0 raw5399; decide +kernel
      have hl : raw5399step0Labels = raw5399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5399 raw5399Labels permutation265 hz
    mixedMoment B raw5399step0 raw5399step0Labels = mixedMoment B raw5399step1 raw5399step1Labels := by
      have ha : raw5399step1 = (fun i j => raw5399step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5399step1 raw5399step0; decide +kernel
      have hl : raw5399step1Labels = raw5399step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5399step0 raw5399step0Labels permutation38 permutation2
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical5400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5400 raw5400Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw5400 raw5400Labels = mixedMoment B raw5400step0 raw5400step0Labels := by
      have ha : raw5400step0 = (fun i j => raw5400 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5400step0 raw5400; decide +kernel
      have hl : raw5400step0Labels = raw5400Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5400 raw5400Labels permutation682 permutation2
    mixedMoment B raw5400step0 raw5400step0Labels = mixedMoment B raw5400step1 raw5400step1Labels := by
      have ha : raw5400step1 = -raw5400step0 := by apply Matrix.ext; change ∀ i j, raw5400step1 i j = -(raw5400step0 i j); unfold raw5400step1 raw5400step0; decide +kernel
      have hl : raw5400step1Labels = raw5400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical5401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5401 raw5401Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw5401 raw5401Labels = mixedMoment B raw5401step0 raw5401step0Labels := by
      have hz : ∀ j, raw5401 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5401step0 = (fun i j => raw5401 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5401step0 raw5401; decide +kernel
      have hl : raw5401step0Labels = raw5401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5401 raw5401Labels permutation265 hz
    mixedMoment B raw5401step0 raw5401step0Labels = mixedMoment B raw5401step1 raw5401step1Labels := by
      have ha : raw5401step1 = (fun i j => raw5401step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5401step1 raw5401step0; decide +kernel
      have hl : raw5401step1Labels = raw5401step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5401step0 raw5401step0Labels permutation151 permutation2
    mixedMoment B raw5401step1 raw5401step1Labels = mixedMoment B raw5401step2 raw5401step2Labels := by
      have ha : raw5401step2 = -raw5401step1 := by apply Matrix.ext; change ∀ i j, raw5401step2 i j = -(raw5401step1 i j); unfold raw5401step2 raw5401step1; decide +kernel
      have hl : raw5401step2Labels = raw5401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical5402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5402 raw5402Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw5402 raw5402Labels = mixedMoment B raw5402step0 raw5402step0Labels := by
      have hz : ∀ j, raw5402 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5402step0 = (fun i j => raw5402 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5402step0 raw5402; decide +kernel
      have hl : raw5402step0Labels = raw5402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5402 raw5402Labels permutation265 hz
    mixedMoment B raw5402step0 raw5402step0Labels = mixedMoment B raw5402step1 raw5402step1Labels := by
      have ha : raw5402step1 = (fun i j => raw5402step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5402step1 raw5402step0; decide +kernel
      have hl : raw5402step1Labels = raw5402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5402step0 raw5402step0Labels permutation149 permutation2
    mixedMoment B raw5402step1 raw5402step1Labels = mixedMoment B raw5402step2 raw5402step2Labels := by
      have ha : raw5402step2 = -raw5402step1 := by apply Matrix.ext; change ∀ i j, raw5402step2 i j = -(raw5402step1 i j); unfold raw5402step2 raw5402step1; decide +kernel
      have hl : raw5402step2Labels = raw5402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical5403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5403 raw5403Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw5403 raw5403Labels = mixedMoment B raw5403step0 raw5403step0Labels := by
      have hz : ∀ j, raw5403 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5403step0 = (fun i j => raw5403 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5403step0 raw5403; decide +kernel
      have hl : raw5403step0Labels = raw5403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5403 raw5403Labels permutation265 hz
    mixedMoment B raw5403step0 raw5403step0Labels = mixedMoment B raw5403step1 raw5403step1Labels := by
      have ha : raw5403step1 = (fun i j => raw5403step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5403step1 raw5403step0; decide +kernel
      have hl : raw5403step1Labels = raw5403step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5403step0 raw5403step0Labels permutation91 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical5404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5404 raw5404Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw5404 raw5404Labels = mixedMoment B raw5404step0 raw5404step0Labels := by
      have hz : ∀ j, raw5404 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5404step0 = (fun i j => raw5404 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5404step0 raw5404; decide +kernel
      have hl : raw5404step0Labels = raw5404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5404 raw5404Labels permutation265 hz
    mixedMoment B raw5404step0 raw5404step0Labels = mixedMoment B raw5404step1 raw5404step1Labels := by
      have ha : raw5404step1 = (fun i j => raw5404step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5404step1 raw5404step0; decide +kernel
      have hl : raw5404step1Labels = raw5404step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5404step0 raw5404step0Labels permutation89 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical5405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5405 raw5405Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw5405 raw5405Labels = mixedMoment B raw5405step0 raw5405step0Labels := by
      have hz : ∀ j, raw5405 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5405step0 = (fun i j => raw5405 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5405step0 raw5405; decide +kernel
      have hl : raw5405step0Labels = raw5405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5405 raw5405Labels permutation265 hz
    mixedMoment B raw5405step0 raw5405step0Labels = mixedMoment B raw5405step1 raw5405step1Labels := by
      have hz : ∀ j, raw5405step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw5405step1 = (fun i j => raw5405step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw5405step1 raw5405step0; decide +kernel
      have hl : raw5405step1Labels = raw5405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5405step0 raw5405step0Labels permutation32 hz
    mixedMoment B raw5405step1 raw5405step1Labels = mixedMoment B raw5405step2 raw5405step2Labels := by
      have ha : raw5405step2 = (fun i j => raw5405step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5405step2 raw5405step1; decide +kernel
      have hl : raw5405step2Labels = raw5405step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5405step1 raw5405step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical5406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5406 raw5406Labels = mixedMoment B node1463 node1463Labels := by
  calc
    mixedMoment B raw5406 raw5406Labels = mixedMoment B raw5406step0 raw5406step0Labels := by
      have ha : raw5406step0 = (fun i j => raw5406 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5406step0 raw5406; decide +kernel
      have hl : raw5406step0Labels = raw5406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5406 raw5406Labels permutation206 permutation2
    _ = mixedMoment B node1463 node1463Labels := by rfl

theorem canonical5407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5407 raw5407Labels = mixedMoment B node1466 node1466Labels := by
  calc
    mixedMoment B raw5407 raw5407Labels = mixedMoment B raw5407step0 raw5407step0Labels := by
      have hz : ∀ j, raw5407 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5407step0 = (fun i j => raw5407 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5407step0 raw5407; decide +kernel
      have hl : raw5407step0Labels = raw5407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5407 raw5407Labels permutation265 hz
    mixedMoment B raw5407step0 raw5407step0Labels = mixedMoment B raw5407step1 raw5407step1Labels := by
      have ha : raw5407step1 = (fun i j => raw5407step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5407step1 raw5407step0; decide +kernel
      have hl : raw5407step1Labels = raw5407step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5407step0 raw5407step0Labels permutation54 permutation4
    mixedMoment B raw5407step1 raw5407step1Labels = mixedMoment B raw5407step2 raw5407step2Labels := by
      have ha : raw5407step2 = -raw5407step1 := by apply Matrix.ext; change ∀ i j, raw5407step2 i j = -(raw5407step1 i j); unfold raw5407step2 raw5407step1; decide +kernel
      have hl : raw5407step2Labels = raw5407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1466 node1466Labels := by rfl

theorem canonical5408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5408 raw5408Labels = mixedMoment B node1465 node1465Labels := by
  calc
    mixedMoment B raw5408 raw5408Labels = mixedMoment B raw5408step0 raw5408step0Labels := by
      have hz : ∀ j, raw5408 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5408step0 = (fun i j => raw5408 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5408step0 raw5408; decide +kernel
      have hl : raw5408step0Labels = raw5408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5408 raw5408Labels permutation265 hz
    mixedMoment B raw5408step0 raw5408step0Labels = mixedMoment B raw5408step1 raw5408step1Labels := by
      have ha : raw5408step1 = (fun i j => raw5408step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5408step1 raw5408step0; decide +kernel
      have hl : raw5408step1Labels = raw5408step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5408step0 raw5408step0Labels permutation54 permutation4
    mixedMoment B raw5408step1 raw5408step1Labels = mixedMoment B raw5408step2 raw5408step2Labels := by
      have ha : raw5408step2 = -raw5408step1 := by apply Matrix.ext; change ∀ i j, raw5408step2 i j = -(raw5408step1 i j); unfold raw5408step2 raw5408step1; decide +kernel
      have hl : raw5408step2Labels = raw5408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1465 node1465Labels := by rfl

theorem canonical5409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5409 raw5409Labels = mixedMoment B node1466 node1466Labels := by
  calc
    mixedMoment B raw5409 raw5409Labels = mixedMoment B raw5409step0 raw5409step0Labels := by
      have hz : ∀ j, raw5409 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5409step0 = (fun i j => raw5409 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5409step0 raw5409; decide +kernel
      have hl : raw5409step0Labels = raw5409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5409 raw5409Labels permutation265 hz
    mixedMoment B raw5409step0 raw5409step0Labels = mixedMoment B raw5409step1 raw5409step1Labels := by
      have ha : raw5409step1 = (fun i j => raw5409step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5409step1 raw5409step0; decide +kernel
      have hl : raw5409step1Labels = raw5409step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5409step0 raw5409step0Labels permutation38 permutation2
    _ = mixedMoment B node1466 node1466Labels := by rfl

theorem canonical5410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5410 raw5410Labels = mixedMoment B node1465 node1465Labels := by
  calc
    mixedMoment B raw5410 raw5410Labels = mixedMoment B raw5410step0 raw5410step0Labels := by
      have hz : ∀ j, raw5410 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5410step0 = (fun i j => raw5410 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5410step0 raw5410; decide +kernel
      have hl : raw5410step0Labels = raw5410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5410 raw5410Labels permutation265 hz
    mixedMoment B raw5410step0 raw5410step0Labels = mixedMoment B raw5410step1 raw5410step1Labels := by
      have ha : raw5410step1 = (fun i j => raw5410step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5410step1 raw5410step0; decide +kernel
      have hl : raw5410step1Labels = raw5410step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5410step0 raw5410step0Labels permutation38 permutation2
    _ = mixedMoment B node1465 node1465Labels := by rfl

theorem canonical5411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5411 raw5411Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw5411 raw5411Labels = mixedMoment B raw5411step0 raw5411step0Labels := by
      have ha : raw5411step0 = (fun i j => raw5411 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5411step0 raw5411; decide +kernel
      have hl : raw5411step0Labels = raw5411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5411 raw5411Labels permutation182 permutation2
    _ = mixedMoment B node3196 node3196Labels := by rfl

theorem canonical5412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5412 raw5412Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5412 raw5412Labels = mixedMoment B raw5412step0 raw5412step0Labels := by
      have ha : raw5412step0 = (fun i j => raw5412 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5412step0 raw5412; decide +kernel
      have hl : raw5412step0Labels = raw5412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5412 raw5412Labels permutation206 permutation2
    _ = mixedMoment B node3170 node3170Labels := by rfl

theorem canonical5413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5413 raw5413Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw5413 raw5413Labels = mixedMoment B raw5413step0 raw5413step0Labels := by
      have ha : raw5413step0 = (fun i j => raw5413 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5413step0 raw5413; decide +kernel
      have hl : raw5413step0Labels = raw5413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5413 raw5413Labels permutation240 permutation4
    mixedMoment B raw5413step0 raw5413step0Labels = mixedMoment B raw5413step1 raw5413step1Labels := by
      have ha : raw5413step1 = -raw5413step0 := by apply Matrix.ext; change ∀ i j, raw5413step1 i j = -(raw5413step0 i j); unfold raw5413step1 raw5413step0; decide +kernel
      have hl : raw5413step1Labels = raw5413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3196 node3196Labels := by rfl

theorem canonical5414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5414 raw5414Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw5414 raw5414Labels = mixedMoment B raw5414step0 raw5414step0Labels := by
      have ha : raw5414step0 = (fun i j => raw5414 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5414step0 raw5414; decide +kernel
      have hl : raw5414step0Labels = raw5414Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5414 raw5414Labels permutation260 permutation4
    mixedMoment B raw5414step0 raw5414step0Labels = mixedMoment B raw5414step1 raw5414step1Labels := by
      have ha : raw5414step1 = -raw5414step0 := by apply Matrix.ext; change ∀ i j, raw5414step1 i j = -(raw5414step0 i j); unfold raw5414step1 raw5414step0; decide +kernel
      have hl : raw5414step1Labels = raw5414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3170 node3170Labels := by rfl

theorem canonical5415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5415 raw5415Labels = mixedMoment B node3217 node3217Labels := by
  calc
    mixedMoment B raw5415 raw5415Labels = mixedMoment B raw5415step0 raw5415step0Labels := by
      have ha : raw5415step0 = (fun i j => raw5415 (permutation174 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5415step0 raw5415; decide +kernel
      have hl : raw5415step0Labels = raw5415Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5415 raw5415Labels permutation174 permutation4
    mixedMoment B raw5415step0 raw5415step0Labels = mixedMoment B raw5415step1 raw5415step1Labels := by
      have ha : raw5415step1 = -raw5415step0 := by apply Matrix.ext; change ∀ i j, raw5415step1 i j = -(raw5415step0 i j); unfold raw5415step1 raw5415step0; decide +kernel
      have hl : raw5415step1Labels = raw5415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3217 node3217Labels := by rfl

theorem canonical5416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5416 raw5416Labels = mixedMoment B node2474 node2474Labels := by
  calc
    mixedMoment B raw5416 raw5416Labels = mixedMoment B raw5416step0 raw5416step0Labels := by
      have ha : raw5416step0 = (fun i j => raw5416 (permutation480 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5416step0 raw5416; decide +kernel
      have hl : raw5416step0Labels = raw5416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5416 raw5416Labels permutation480 permutation4
    _ = mixedMoment B node2474 node2474Labels := by rfl

theorem canonical5417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5417 raw5417Labels = mixedMoment B node3217 node3217Labels := by
  calc
    mixedMoment B raw5417 raw5417Labels = mixedMoment B raw5417step0 raw5417step0Labels := by
      have ha : raw5417step0 = (fun i j => raw5417 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5417step0 raw5417; decide +kernel
      have hl : raw5417step0Labels = raw5417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5417 raw5417Labels permutation158 permutation2
    _ = mixedMoment B node3217 node3217Labels := by rfl

theorem canonical5418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5418 raw5418Labels = mixedMoment B node2474 node2474Labels := by
  calc
    mixedMoment B raw5418 raw5418Labels = mixedMoment B raw5418step0 raw5418step0Labels := by
      have ha : raw5418step0 = (fun i j => raw5418 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5418step0 raw5418; decide +kernel
      have hl : raw5418step0Labels = raw5418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5418 raw5418Labels permutation682 permutation2
    mixedMoment B raw5418step0 raw5418step0Labels = mixedMoment B raw5418step1 raw5418step1Labels := by
      have ha : raw5418step1 = -raw5418step0 := by apply Matrix.ext; change ∀ i j, raw5418step1 i j = -(raw5418step0 i j); unfold raw5418step1 raw5418step0; decide +kernel
      have hl : raw5418step1Labels = raw5418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2474 node2474Labels := by rfl

theorem canonical5419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5419 raw5419Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw5419 raw5419Labels = mixedMoment B raw5419step0 raw5419step0Labels := by
      have hz : ∀ j, raw5419 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5419step0 = (fun i j => raw5419 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5419step0 raw5419; decide +kernel
      have hl : raw5419step0Labels = raw5419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5419 raw5419Labels permutation265 hz
    mixedMoment B raw5419step0 raw5419step0Labels = mixedMoment B raw5419step1 raw5419step1Labels := by
      have ha : raw5419step1 = (fun i j => raw5419step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5419step1 raw5419step0; decide +kernel
      have hl : raw5419step1Labels = raw5419step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5419step0 raw5419step0Labels permutation38 permutation2
    _ = mixedMoment B node3180 node3180Labels := by rfl

theorem canonical5420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5420 raw5420Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw5420 raw5420Labels = mixedMoment B raw5420step0 raw5420step0Labels := by
      have hz : ∀ j, raw5420 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5420step0 = (fun i j => raw5420 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5420step0 raw5420; decide +kernel
      have hl : raw5420step0Labels = raw5420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5420 raw5420Labels permutation265 hz
    mixedMoment B raw5420step0 raw5420step0Labels = mixedMoment B raw5420step1 raw5420step1Labels := by
      have ha : raw5420step1 = (fun i j => raw5420step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5420step1 raw5420step0; decide +kernel
      have hl : raw5420step1Labels = raw5420step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5420step0 raw5420step0Labels permutation48 permutation4
    mixedMoment B raw5420step1 raw5420step1Labels = mixedMoment B raw5420step2 raw5420step2Labels := by
      have ha : raw5420step2 = -raw5420step1 := by apply Matrix.ext; change ∀ i j, raw5420step2 i j = -(raw5420step1 i j); unfold raw5420step2 raw5420step1; decide +kernel
      have hl : raw5420step2Labels = raw5420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3198 node3198Labels := by rfl

theorem canonical5421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5421 raw5421Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw5421 raw5421Labels = mixedMoment B raw5421step0 raw5421step0Labels := by
      have hz : ∀ j, raw5421 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5421step0 = (fun i j => raw5421 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5421step0 raw5421; decide +kernel
      have hl : raw5421step0Labels = raw5421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5421 raw5421Labels permutation265 hz
    mixedMoment B raw5421step0 raw5421step0Labels = mixedMoment B raw5421step1 raw5421step1Labels := by
      have ha : raw5421step1 = (fun i j => raw5421step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5421step1 raw5421step0; decide +kernel
      have hl : raw5421step1Labels = raw5421step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5421step0 raw5421step0Labels permutation54 permutation4
    mixedMoment B raw5421step1 raw5421step1Labels = mixedMoment B raw5421step2 raw5421step2Labels := by
      have ha : raw5421step2 = -raw5421step1 := by apply Matrix.ext; change ∀ i j, raw5421step2 i j = -(raw5421step1 i j); unfold raw5421step2 raw5421step1; decide +kernel
      have hl : raw5421step2Labels = raw5421step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3174 node3174Labels := by rfl

theorem canonical5422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5422 raw5422Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw5422 raw5422Labels = mixedMoment B raw5422step0 raw5422step0Labels := by
      have hz : ∀ j, raw5422 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5422step0 = (fun i j => raw5422 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5422step0 raw5422; decide +kernel
      have hl : raw5422step0Labels = raw5422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5422 raw5422Labels permutation265 hz
    mixedMoment B raw5422step0 raw5422step0Labels = mixedMoment B raw5422step1 raw5422step1Labels := by
      have ha : raw5422step1 = (fun i j => raw5422step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5422step1 raw5422step0; decide +kernel
      have hl : raw5422step1Labels = raw5422step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5422step0 raw5422step0Labels permutation89 permutation4
    _ = mixedMoment B node2716 node2716Labels := by rfl

theorem canonical5423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5423 raw5423Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw5423 raw5423Labels = mixedMoment B raw5423step0 raw5423step0Labels := by
      have hz : ∀ j, raw5423 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5423step0 = (fun i j => raw5423 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5423step0 raw5423; decide +kernel
      have hl : raw5423step0Labels = raw5423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5423 raw5423Labels permutation265 hz
    _ = mixedMoment B node3198 node3198Labels := by rfl

theorem canonical5424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5424 raw5424Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw5424 raw5424Labels = mixedMoment B raw5424step0 raw5424step0Labels := by
      have hz : ∀ j, raw5424 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5424step0 = (fun i j => raw5424 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5424step0 raw5424; decide +kernel
      have hl : raw5424step0Labels = raw5424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5424 raw5424Labels permutation265 hz
    mixedMoment B raw5424step0 raw5424step0Labels = mixedMoment B raw5424step1 raw5424step1Labels := by
      have ha : raw5424step1 = (fun i j => raw5424step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5424step1 raw5424step0; decide +kernel
      have hl : raw5424step1Labels = raw5424step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5424step0 raw5424step0Labels permutation151 permutation2
    mixedMoment B raw5424step1 raw5424step1Labels = mixedMoment B raw5424step2 raw5424step2Labels := by
      have ha : raw5424step2 = -raw5424step1 := by apply Matrix.ext; change ∀ i j, raw5424step2 i j = -(raw5424step1 i j); unfold raw5424step2 raw5424step1; decide +kernel
      have hl : raw5424step2Labels = raw5424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2497 node2497Labels := by rfl

theorem canonical5425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5425 raw5425Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw5425 raw5425Labels = mixedMoment B raw5425step0 raw5425step0Labels := by
      have hz : ∀ j, raw5425 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5425step0 = (fun i j => raw5425 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5425step0 raw5425; decide +kernel
      have hl : raw5425step0Labels = raw5425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5425 raw5425Labels permutation265 hz
    mixedMoment B raw5425step0 raw5425step0Labels = mixedMoment B raw5425step1 raw5425step1Labels := by
      have ha : raw5425step1 = (fun i j => raw5425step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5425step1 raw5425step0; decide +kernel
      have hl : raw5425step1Labels = raw5425step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5425step0 raw5425step0Labels permutation91 permutation4
    _ = mixedMoment B node2497 node2497Labels := by rfl

theorem canonical5426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5426 raw5426Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw5426 raw5426Labels = mixedMoment B raw5426step0 raw5426step0Labels := by
      have hz : ∀ j, raw5426 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5426step0 = (fun i j => raw5426 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5426step0 raw5426; decide +kernel
      have hl : raw5426step0Labels = raw5426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5426 raw5426Labels permutation265 hz
    mixedMoment B raw5426step0 raw5426step0Labels = mixedMoment B raw5426step1 raw5426step1Labels := by
      have ha : raw5426step1 = (fun i j => raw5426step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5426step1 raw5426step0; decide +kernel
      have hl : raw5426step1Labels = raw5426step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5426step0 raw5426step0Labels permutation89 permutation4
    _ = mixedMoment B node2486 node2486Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5517 raw5517Labels = mixedMoment B node2233 node2233Labels := by
  calc
    _ = mixedMoment B node2233 node2233Labels := by rfl

theorem canonical5518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5518 raw5518Labels = mixedMoment B node3567 node3567Labels := by
  calc
    _ = mixedMoment B node3567 node3567Labels := by rfl

theorem canonical5519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5519 raw5519Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw5519 raw5519Labels = mixedMoment B raw5519step0 raw5519step0Labels := by
      have ha : raw5519step0 = (fun i j => raw5519 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5519step0 raw5519; decide +kernel
      have hl : raw5519step0Labels = raw5519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5519 raw5519Labels permutation176 permutation2
    _ = mixedMoment B node3567 node3567Labels := by rfl

theorem canonical5520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5520 raw5520Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw5520 raw5520Labels = mixedMoment B raw5520step0 raw5520step0Labels := by
      have ha : raw5520step0 = (fun i j => raw5520 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5520step0 raw5520; decide +kernel
      have hl : raw5520step0Labels = raw5520Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5520 raw5520Labels permutation200 permutation2
    _ = mixedMoment B node3567 node3567Labels := by rfl

theorem canonical5521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5521 raw5521Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw5521 raw5521Labels = mixedMoment B raw5521step0 raw5521step0Labels := by
      have hz : ∀ j, raw5521 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5521step0 = (fun i j => raw5521 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5521step0 raw5521; decide +kernel
      have hl : raw5521step0Labels = raw5521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5521 raw5521Labels permutation520 hz
    _ = mixedMoment B node3619 node3619Labels := by rfl

theorem canonical5522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5522 raw5522Labels = mixedMoment B node3618 node3618Labels := by
  calc
    _ = mixedMoment B node3618 node3618Labels := by rfl

theorem canonical5523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5523 raw5523Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw5523 raw5523Labels = mixedMoment B raw5523step0 raw5523step0Labels := by
      have hz : ∀ j, raw5523 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5523step0 = (fun i j => raw5523 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5523step0 raw5523; decide +kernel
      have hl : raw5523step0Labels = raw5523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5523 raw5523Labels permutation590 hz
    mixedMoment B raw5523step0 raw5523step0Labels = mixedMoment B raw5523step1 raw5523step1Labels := by
      have hz : ∀ j, raw5523step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw5523step1 = (fun i j => raw5523step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw5523step1 raw5523step0; decide +kernel
      have hl : raw5523step1Labels = raw5523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5523step0 raw5523step0Labels permutation128 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical5524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5524 raw5524Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw5524 raw5524Labels = mixedMoment B raw5524step0 raw5524step0Labels := by
      have ha : raw5524step0 = (fun i j => raw5524 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5524step0 raw5524; decide +kernel
      have hl : raw5524step0Labels = raw5524Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5524 raw5524Labels permutation184 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

theorem canonical5525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5525 raw5525Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw5525 raw5525Labels = mixedMoment B raw5525step0 raw5525step0Labels := by
      have ha : raw5525step0 = (fun i j => raw5525 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5525step0 raw5525; decide +kernel
      have hl : raw5525step0Labels = raw5525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5525 raw5525Labels permutation160 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

theorem canonical5526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5526 raw5526Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw5526 raw5526Labels = mixedMoment B raw5526step0 raw5526step0Labels := by
      have ha : raw5526step0 = (fun i j => raw5526 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5526step0 raw5526; decide +kernel
      have hl : raw5526step0Labels = raw5526Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5526 raw5526Labels permutation154 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

theorem canonical5527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5527 raw5527Labels = mixedMoment B node1015 node1015Labels := by
  calc
    _ = mixedMoment B node1015 node1015Labels := by rfl

theorem canonical5528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5528 raw5528Labels = mixedMoment B node1014 node1014Labels := by
  calc
    _ = mixedMoment B node1014 node1014Labels := by rfl

theorem canonical5529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5529 raw5529Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5529 raw5529Labels = mixedMoment B raw5529step0 raw5529step0Labels := by
      have ha : raw5529step0 = (fun i j => raw5529 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5529step0 raw5529; decide +kernel
      have hl : raw5529step0Labels = raw5529Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5529 raw5529Labels permutation184 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical5530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5530 raw5530Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5530 raw5530Labels = mixedMoment B raw5530step0 raw5530step0Labels := by
      have ha : raw5530step0 = (fun i j => raw5530 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5530step0 raw5530; decide +kernel
      have hl : raw5530step0Labels = raw5530Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5530 raw5530Labels permutation208 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical5531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5531 raw5531Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw5531 raw5531Labels = mixedMoment B raw5531step0 raw5531step0Labels := by
      have hz : ∀ j, raw5531 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5531step0 = (fun i j => raw5531 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5531step0 raw5531; decide +kernel
      have hl : raw5531step0Labels = raw5531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5531 raw5531Labels permutation520 hz
    mixedMoment B raw5531step0 raw5531step0Labels = mixedMoment B raw5531step1 raw5531step1Labels := by
      have ha : raw5531step1 = (fun i j => raw5531step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5531step1 raw5531step0; decide +kernel
      have hl : raw5531step1Labels = raw5531step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5531step0 raw5531step0Labels permutation40 permutation2
    _ = mixedMoment B node2245 node2245Labels := by rfl

theorem canonical5532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5532 raw5532Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5532 raw5532Labels = mixedMoment B raw5532step0 raw5532step0Labels := by
      have ha : raw5532step0 = (fun i j => raw5532 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5532step0 raw5532; decide +kernel
      have hl : raw5532step0Labels = raw5532Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5532 raw5532Labels permutation185 permutation2
    _ = mixedMoment B node2243 node2243Labels := by rfl

theorem canonical5533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5533 raw5533Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5533 raw5533Labels = mixedMoment B raw5533step0 raw5533step0Labels := by
      have ha : raw5533step0 = (fun i j => raw5533 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5533step0 raw5533; decide +kernel
      have hl : raw5533step0Labels = raw5533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5533 raw5533Labels permutation160 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical5534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5534 raw5534Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5534 raw5534Labels = mixedMoment B raw5534step0 raw5534step0Labels := by
      have ha : raw5534step0 = (fun i j => raw5534 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5534step0 raw5534; decide +kernel
      have hl : raw5534step0Labels = raw5534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5534 raw5534Labels permutation154 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical5535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5535 raw5535Labels = mixedMoment B node2084 node2084Labels := by
  calc
    _ = mixedMoment B node2084 node2084Labels := by rfl

theorem canonical5536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5536 raw5536Labels = mixedMoment B node2083 node2083Labels := by
  calc
    _ = mixedMoment B node2083 node2083Labels := by rfl

theorem canonical5537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5537 raw5537Labels = mixedMoment B node2084 node2084Labels := by
  calc
    mixedMoment B raw5537 raw5537Labels = mixedMoment B raw5537step0 raw5537step0Labels := by
      have ha : raw5537step0 = (fun i j => raw5537 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5537step0 raw5537; decide +kernel
      have hl : raw5537step0Labels = raw5537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5537 raw5537Labels permutation176 permutation2
    _ = mixedMoment B node2084 node2084Labels := by rfl

theorem canonical5538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5538 raw5538Labels = mixedMoment B node2084 node2084Labels := by
  calc
    mixedMoment B raw5538 raw5538Labels = mixedMoment B raw5538step0 raw5538step0Labels := by
      have ha : raw5538step0 = (fun i j => raw5538 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5538step0 raw5538; decide +kernel
      have hl : raw5538step0Labels = raw5538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5538 raw5538Labels permutation200 permutation2
    _ = mixedMoment B node2084 node2084Labels := by rfl

theorem canonical5539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5539 raw5539Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw5539 raw5539Labels = mixedMoment B raw5539step0 raw5539step0Labels := by
      have ha : raw5539step0 = (fun i j => raw5539 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5539step0 raw5539; decide +kernel
      have hl : raw5539step0Labels = raw5539Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5539 raw5539Labels permutation153 permutation2
    _ = mixedMoment B node2233 node2233Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5768 raw5768Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5768 raw5768Labels = mixedMoment B raw5768step0 raw5768step0Labels := by
      have hz : ∀ j, raw5768 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5768step0 = (fun i j => raw5768 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5768step0 raw5768; decide +kernel
      have hl : raw5768step0Labels = raw5768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5768 raw5768Labels permutation265 hz
    mixedMoment B raw5768step0 raw5768step0Labels = mixedMoment B raw5768step1 raw5768step1Labels := by
      have ha : raw5768step1 = (fun i j => raw5768step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5768step1 raw5768step0; decide +kernel
      have hl : raw5768step1Labels = raw5768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5768step0 raw5768step0Labels permutation44 permutation4
    mixedMoment B raw5768step1 raw5768step1Labels = mixedMoment B raw5768step2 raw5768step2Labels := by
      have ha : raw5768step2 = -raw5768step1 := by apply Matrix.ext; change ∀ i j, raw5768step2 i j = -(raw5768step1 i j); unfold raw5768step2 raw5768step1; decide +kernel
      have hl : raw5768step2Labels = raw5768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical5769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5769 raw5769Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5769 raw5769Labels = mixedMoment B raw5769step0 raw5769step0Labels := by
      have hz : ∀ j, raw5769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5769step0 = (fun i j => raw5769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5769step0 raw5769; decide +kernel
      have hl : raw5769step0Labels = raw5769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5769 raw5769Labels permutation346 hz
    mixedMoment B raw5769step0 raw5769step0Labels = mixedMoment B raw5769step1 raw5769step1Labels := by
      have ha : raw5769step1 = (fun i j => raw5769step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5769step1 raw5769step0; decide +kernel
      have hl : raw5769step1Labels = raw5769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5769step0 raw5769step0Labels permutation44 permutation4
    mixedMoment B raw5769step1 raw5769step1Labels = mixedMoment B raw5769step2 raw5769step2Labels := by
      have ha : raw5769step2 = -raw5769step1 := by apply Matrix.ext; change ∀ i j, raw5769step2 i j = -(raw5769step1 i j); unfold raw5769step2 raw5769step1; decide +kernel
      have hl : raw5769step2Labels = raw5769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6787 raw6787Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw6787 raw6787Labels = mixedMoment B raw6787step0 raw6787step0Labels := by
      have hz : ∀ j, raw6787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6787step0 = (fun i j => raw6787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6787step0 raw6787; decide +kernel
      have hl : raw6787step0Labels = raw6787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6787 raw6787Labels permutation346 hz
    mixedMoment B raw6787step0 raw6787step0Labels = mixedMoment B raw6787step1 raw6787step1Labels := by
      have ha : raw6787step1 = (fun i j => raw6787step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6787step1 raw6787step0; decide +kernel
      have hl : raw6787step1Labels = raw6787step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6787step0 raw6787step0Labels permutation38 permutation2
    mixedMoment B raw6787step1 raw6787step1Labels = mixedMoment B raw6787step2 raw6787step2Labels := by
      have ha : raw6787step2 = -raw6787step1 := by apply Matrix.ext; change ∀ i j, raw6787step2 i j = -(raw6787step1 i j); unfold raw6787step2 raw6787step1; decide +kernel
      have hl : raw6787step2Labels = raw6787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical6790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6790 raw6790Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw6790 raw6790Labels = mixedMoment B raw6790step0 raw6790step0Labels := by
      have hz : ∀ j, raw6790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6790step0 = (fun i j => raw6790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6790step0 raw6790; decide +kernel
      have hl : raw6790step0Labels = raw6790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790 raw6790Labels permutation346 hz
    mixedMoment B raw6790step0 raw6790step0Labels = mixedMoment B raw6790step1 raw6790step1Labels := by
      have hz : ∀ j, raw6790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6790step1 = (fun i j => raw6790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6790step1 raw6790step0; decide +kernel
      have hl : raw6790step1Labels = raw6790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790step0 raw6790step0Labels permutation56 hz
    mixedMoment B raw6790step1 raw6790step1Labels = mixedMoment B raw6790step2 raw6790step2Labels := by
      have ha : raw6790step2 = (fun i j => raw6790step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6790step2 raw6790step1; decide +kernel
      have hl : raw6790step2Labels = raw6790step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6790step1 raw6790step1Labels permutation11 permutation4
    mixedMoment B raw6790step2 raw6790step2Labels = mixedMoment B raw6790step3 raw6790step3Labels := by
      have ha : raw6790step3 = -raw6790step2 := by apply Matrix.ext; change ∀ i j, raw6790step3 i j = -(raw6790step2 i j); unfold raw6790step3 raw6790step2; decide +kernel
      have hl : raw6790step3Labels = raw6790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical6796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6796 raw6796Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw6796 raw6796Labels = mixedMoment B raw6796step0 raw6796step0Labels := by
      have hz : ∀ j, raw6796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6796step0 = (fun i j => raw6796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6796step0 raw6796; decide +kernel
      have hl : raw6796step0Labels = raw6796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796 raw6796Labels permutation346 hz
    mixedMoment B raw6796step0 raw6796step0Labels = mixedMoment B raw6796step1 raw6796step1Labels := by
      have hz : ∀ j, raw6796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6796step1 = (fun i j => raw6796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6796step1 raw6796step0; decide +kernel
      have hl : raw6796step1Labels = raw6796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796step0 raw6796step0Labels permutation56 hz
    mixedMoment B raw6796step1 raw6796step1Labels = mixedMoment B raw6796step2 raw6796step2Labels := by
      have ha : raw6796step2 = (fun i j => raw6796step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6796step2 raw6796step1; decide +kernel
      have hl : raw6796step2Labels = raw6796step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6796step1 raw6796step1Labels permutation10 permutation4
    mixedMoment B raw6796step2 raw6796step2Labels = mixedMoment B raw6796step3 raw6796step3Labels := by
      have ha : raw6796step3 = -raw6796step2 := by apply Matrix.ext; change ∀ i j, raw6796step3 i j = -(raw6796step2 i j); unfold raw6796step3 raw6796step2; decide +kernel
      have hl : raw6796step3Labels = raw6796step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

theorem canonical6797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6797 raw6797Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw6797 raw6797Labels = mixedMoment B raw6797step0 raw6797step0Labels := by
      have hz : ∀ j, raw6797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6797step0 = (fun i j => raw6797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6797step0 raw6797; decide +kernel
      have hl : raw6797step0Labels = raw6797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797 raw6797Labels permutation346 hz
    mixedMoment B raw6797step0 raw6797step0Labels = mixedMoment B raw6797step1 raw6797step1Labels := by
      have hz : ∀ j, raw6797step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6797step1 = (fun i j => raw6797step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6797step1 raw6797step0; decide +kernel
      have hl : raw6797step1Labels = raw6797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797step0 raw6797step0Labels permutation56 hz
    mixedMoment B raw6797step1 raw6797step1Labels = mixedMoment B raw6797step2 raw6797step2Labels := by
      have ha : raw6797step2 = (fun i j => raw6797step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6797step2 raw6797step1; decide +kernel
      have hl : raw6797step2Labels = raw6797step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6797step1 raw6797step1Labels permutation11 permutation4
    mixedMoment B raw6797step2 raw6797step2Labels = mixedMoment B raw6797step3 raw6797step3Labels := by
      have ha : raw6797step3 = -raw6797step2 := by apply Matrix.ext; change ∀ i j, raw6797step3 i j = -(raw6797step2 i j); unfold raw6797step3 raw6797step2; decide +kernel
      have hl : raw6797step3Labels = raw6797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical6811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6811 raw6811Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6811 raw6811Labels = mixedMoment B raw6811step0 raw6811step0Labels := by
      have hz : ∀ j, raw6811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6811step0 = (fun i j => raw6811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6811step0 raw6811; decide +kernel
      have hl : raw6811step0Labels = raw6811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6811 raw6811Labels permutation346 hz
    mixedMoment B raw6811step0 raw6811step0Labels = mixedMoment B raw6811step1 raw6811step1Labels := by
      have ha : raw6811step1 = (fun i j => raw6811step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6811step1 raw6811step0; decide +kernel
      have hl : raw6811step1Labels = raw6811step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6811step0 raw6811step0Labels permutation34 permutation4
    mixedMoment B raw6811step1 raw6811step1Labels = mixedMoment B raw6811step2 raw6811step2Labels := by
      have ha : raw6811step2 = -raw6811step1 := by apply Matrix.ext; change ∀ i j, raw6811step2 i j = -(raw6811step1 i j); unfold raw6811step2 raw6811step1; decide +kernel
      have hl : raw6811step2Labels = raw6811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7282 raw7282Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw7282 raw7282Labels = mixedMoment B raw7282step0 raw7282step0Labels := by
      have hz : ∀ j, raw7282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7282step0 = (fun i j => raw7282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7282step0 raw7282; decide +kernel
      have hl : raw7282step0Labels = raw7282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7282 raw7282Labels permutation434 hz
    mixedMoment B raw7282step0 raw7282step0Labels = mixedMoment B raw7282step1 raw7282step1Labels := by
      have hz : ∀ j, raw7282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7282step1 = (fun i j => raw7282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7282step1 raw7282step0; decide +kernel
      have hl : raw7282step1Labels = raw7282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7282step0 raw7282step0Labels permutation56 hz
    mixedMoment B raw7282step1 raw7282step1Labels = mixedMoment B raw7282step2 raw7282step2Labels := by
      have ha : raw7282step2 = (fun i j => raw7282step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7282step2 raw7282step1; decide +kernel
      have hl : raw7282step2Labels = raw7282step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7282step1 raw7282step1Labels permutation10 permutation4
    mixedMoment B raw7282step2 raw7282step2Labels = mixedMoment B raw7282step3 raw7282step3Labels := by
      have ha : raw7282step3 = -raw7282step2 := by apply Matrix.ext; change ∀ i j, raw7282step3 i j = -(raw7282step2 i j); unfold raw7282step3 raw7282step2; decide +kernel
      have hl : raw7282step3Labels = raw7282step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

theorem canonical7283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7283 raw7283Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7283 raw7283Labels = mixedMoment B raw7283step0 raw7283step0Labels := by
      have hz : ∀ j, raw7283 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7283step0 = (fun i j => raw7283 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7283step0 raw7283; decide +kernel
      have hl : raw7283step0Labels = raw7283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7283 raw7283Labels permutation265 hz
    mixedMoment B raw7283step0 raw7283step0Labels = mixedMoment B raw7283step1 raw7283step1Labels := by
      have ha : raw7283step1 = (fun i j => raw7283step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7283step1 raw7283step0; decide +kernel
      have hl : raw7283step1Labels = raw7283step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7283step0 raw7283step0Labels permutation44 permutation4
    mixedMoment B raw7283step1 raw7283step1Labels = mixedMoment B raw7283step2 raw7283step2Labels := by
      have ha : raw7283step2 = -raw7283step1 := by apply Matrix.ext; change ∀ i j, raw7283step2 i j = -(raw7283step1 i j); unfold raw7283step2 raw7283step1; decide +kernel
      have hl : raw7283step2Labels = raw7283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7697 raw7697Labels = mixedMoment B node3635 node3635Labels := by
  calc
    mixedMoment B raw7697 raw7697Labels = mixedMoment B raw7697step0 raw7697step0Labels := by
      have hz : ∀ j, raw7697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7697step0 = (fun i j => raw7697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7697step0 raw7697; decide +kernel
      have hl : raw7697step0Labels = raw7697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697 raw7697Labels permutation434 hz
    mixedMoment B raw7697step0 raw7697step0Labels = mixedMoment B raw7697step1 raw7697step1Labels := by
      have hz : ∀ j, raw7697step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7697step1 = (fun i j => raw7697step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7697step1 raw7697step0; decide +kernel
      have hl : raw7697step1Labels = raw7697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697step0 raw7697step0Labels permutation80 hz
    mixedMoment B raw7697step1 raw7697step1Labels = mixedMoment B raw7697step2 raw7697step2Labels := by
      have hz : ∀ j, raw7697step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7697step2 = (fun i j => raw7697step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7697step2 raw7697step1; decide +kernel
      have hl : raw7697step2Labels = raw7697step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7697step1 raw7697step1Labels permutation14 hz
    mixedMoment B raw7697step2 raw7697step2Labels = mixedMoment B raw7697step3 raw7697step3Labels := by
      have ha : raw7697step3 = (fun i j => raw7697step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7697step3 raw7697step2; decide +kernel
      have hl : raw7697step3Labels = raw7697step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7697step2 raw7697step2Labels permutation2 permutation4
    mixedMoment B raw7697step3 raw7697step3Labels = mixedMoment B raw7697step4 raw7697step4Labels := by
      have ha : raw7697step4 = -raw7697step3 := by apply Matrix.ext; change ∀ i j, raw7697step4 i j = -(raw7697step3 i j); unfold raw7697step4 raw7697step3; decide +kernel
      have hl : raw7697step4Labels = raw7697step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3635 node3635Labels := by rfl

theorem canonical7791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7791 raw7791Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw7791 raw7791Labels = mixedMoment B raw7791step0 raw7791step0Labels := by
      have hz : ∀ j, raw7791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7791step0 = (fun i j => raw7791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7791step0 raw7791; decide +kernel
      have hl : raw7791step0Labels = raw7791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791 raw7791Labels permutation434 hz
    mixedMoment B raw7791step0 raw7791step0Labels = mixedMoment B raw7791step1 raw7791step1Labels := by
      have hz : ∀ j, raw7791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7791step1 = (fun i j => raw7791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7791step1 raw7791step0; decide +kernel
      have hl : raw7791step1Labels = raw7791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791step0 raw7791step0Labels permutation80 hz
    mixedMoment B raw7791step1 raw7791step1Labels = mixedMoment B raw7791step2 raw7791step2Labels := by
      have hz : ∀ j, raw7791step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7791step2 = (fun i j => raw7791step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7791step2 raw7791step1; decide +kernel
      have hl : raw7791step2Labels = raw7791step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7791step1 raw7791step1Labels permutation14 hz
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical7795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7795 raw7795Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw7795 raw7795Labels = mixedMoment B raw7795step0 raw7795step0Labels := by
      have hz : ∀ j, raw7795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7795step0 = (fun i j => raw7795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7795step0 raw7795; decide +kernel
      have hl : raw7795step0Labels = raw7795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795 raw7795Labels permutation434 hz
    mixedMoment B raw7795step0 raw7795step0Labels = mixedMoment B raw7795step1 raw7795step1Labels := by
      have hz : ∀ j, raw7795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7795step1 = (fun i j => raw7795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7795step1 raw7795step0; decide +kernel
      have hl : raw7795step1Labels = raw7795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795step0 raw7795step0Labels permutation80 hz
    mixedMoment B raw7795step1 raw7795step1Labels = mixedMoment B raw7795step2 raw7795step2Labels := by
      have hz : ∀ j, raw7795step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7795step2 = (fun i j => raw7795step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7795step2 raw7795step1; decide +kernel
      have hl : raw7795step2Labels = raw7795step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7795step1 raw7795step1Labels permutation14 hz
    mixedMoment B raw7795step2 raw7795step2Labels = mixedMoment B raw7795step3 raw7795step3Labels := by
      have ha : raw7795step3 = (fun i j => raw7795step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7795step3 raw7795step2; decide +kernel
      have hl : raw7795step3Labels = raw7795step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7795step2 raw7795step2Labels permutation3 permutation2
    _ = mixedMoment B node1310 node1310Labels := by rfl

theorem canonical7797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7797 raw7797Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw7797 raw7797Labels = mixedMoment B raw7797step0 raw7797step0Labels := by
      have hz : ∀ j, raw7797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7797step0 = (fun i j => raw7797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7797step0 raw7797; decide +kernel
      have hl : raw7797step0Labels = raw7797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797 raw7797Labels permutation434 hz
    mixedMoment B raw7797step0 raw7797step0Labels = mixedMoment B raw7797step1 raw7797step1Labels := by
      have hz : ∀ j, raw7797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7797step1 = (fun i j => raw7797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7797step1 raw7797step0; decide +kernel
      have hl : raw7797step1Labels = raw7797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797step0 raw7797step0Labels permutation80 hz
    mixedMoment B raw7797step1 raw7797step1Labels = mixedMoment B raw7797step2 raw7797step2Labels := by
      have hz : ∀ j, raw7797step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7797step2 = (fun i j => raw7797step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7797step2 raw7797step1; decide +kernel
      have hl : raw7797step2Labels = raw7797step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7797step1 raw7797step1Labels permutation14 hz
    mixedMoment B raw7797step2 raw7797step2Labels = mixedMoment B raw7797step3 raw7797step3Labels := by
      have ha : raw7797step3 = (fun i j => raw7797step2 (permutation5 i) (permutation0 j)) := by apply Matrix.ext; unfold raw7797step3 raw7797step2; decide +kernel
      have hl : raw7797step3Labels = raw7797step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7797step2 raw7797step2Labels permutation5 permutation0
    mixedMoment B raw7797step3 raw7797step3Labels = mixedMoment B raw7797step4 raw7797step4Labels := by
      have ha : raw7797step4 = -raw7797step3 := by apply Matrix.ext; change ∀ i j, raw7797step4 i j = -(raw7797step3 i j); unfold raw7797step4 raw7797step3; decide +kernel
      have hl : raw7797step4Labels = raw7797step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical7802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7802 raw7802Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw7802 raw7802Labels = mixedMoment B raw7802step0 raw7802step0Labels := by
      have hz : ∀ j, raw7802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7802step0 = (fun i j => raw7802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7802step0 raw7802; decide +kernel
      have hl : raw7802step0Labels = raw7802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7802 raw7802Labels permutation434 hz
    mixedMoment B raw7802step0 raw7802step0Labels = mixedMoment B raw7802step1 raw7802step1Labels := by
      have hz : ∀ j, raw7802step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7802step1 = (fun i j => raw7802step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7802step1 raw7802step0; decide +kernel
      have hl : raw7802step1Labels = raw7802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7802step0 raw7802step0Labels permutation80 hz
    mixedMoment B raw7802step1 raw7802step1Labels = mixedMoment B raw7802step2 raw7802step2Labels := by
      have ha : raw7802step2 = (fun i j => raw7802step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7802step2 raw7802step1; decide +kernel
      have hl : raw7802step2Labels = raw7802step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7802step1 raw7802step1Labels permutation9 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

theorem canonical7803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7803 raw7803Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw7803 raw7803Labels = mixedMoment B raw7803step0 raw7803step0Labels := by
      have hz : ∀ j, raw7803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7803step0 = (fun i j => raw7803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7803step0 raw7803; decide +kernel
      have hl : raw7803step0Labels = raw7803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7803 raw7803Labels permutation434 hz
    mixedMoment B raw7803step0 raw7803step0Labels = mixedMoment B raw7803step1 raw7803step1Labels := by
      have hz : ∀ j, raw7803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7803step1 = (fun i j => raw7803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7803step1 raw7803step0; decide +kernel
      have hl : raw7803step1Labels = raw7803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7803step0 raw7803step0Labels permutation56 hz
    mixedMoment B raw7803step1 raw7803step1Labels = mixedMoment B raw7803step2 raw7803step2Labels := by
      have ha : raw7803step2 = (fun i j => raw7803step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7803step2 raw7803step1; decide +kernel
      have hl : raw7803step2Labels = raw7803step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7803step1 raw7803step1Labels permutation9 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

theorem canonical7804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7804 raw7804Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw7804 raw7804Labels = mixedMoment B raw7804step0 raw7804step0Labels := by
      have hz : ∀ j, raw7804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7804step0 = (fun i j => raw7804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7804step0 raw7804; decide +kernel
      have hl : raw7804step0Labels = raw7804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7804 raw7804Labels permutation346 hz
    mixedMoment B raw7804step0 raw7804step0Labels = mixedMoment B raw7804step1 raw7804step1Labels := by
      have hz : ∀ j, raw7804step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7804step1 = (fun i j => raw7804step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7804step1 raw7804step0; decide +kernel
      have hl : raw7804step1Labels = raw7804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7804step0 raw7804step0Labels permutation56 hz
    mixedMoment B raw7804step1 raw7804step1Labels = mixedMoment B raw7804step2 raw7804step2Labels := by
      have ha : raw7804step2 = (fun i j => raw7804step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7804step2 raw7804step1; decide +kernel
      have hl : raw7804step2Labels = raw7804step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7804step1 raw7804step1Labels permutation9 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

theorem canonical7805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7805 raw7805Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7805 raw7805Labels = mixedMoment B raw7805step0 raw7805step0Labels := by
      have hz : ∀ j, raw7805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7805step0 = (fun i j => raw7805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7805step0 raw7805; decide +kernel
      have hl : raw7805step0Labels = raw7805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7805 raw7805Labels permutation434 hz
    mixedMoment B raw7805step0 raw7805step0Labels = mixedMoment B raw7805step1 raw7805step1Labels := by
      have hz : ∀ j, raw7805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7805step1 = (fun i j => raw7805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7805step1 raw7805step0; decide +kernel
      have hl : raw7805step1Labels = raw7805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7805step0 raw7805step0Labels permutation80 hz
    mixedMoment B raw7805step1 raw7805step1Labels = mixedMoment B raw7805step2 raw7805step2Labels := by
      have hz : ∀ j, raw7805step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7805step2 = (fun i j => raw7805step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7805step2 raw7805step1; decide +kernel
      have hl : raw7805step2Labels = raw7805step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7805step1 raw7805step1Labels permutation14 hz
    mixedMoment B raw7805step2 raw7805step2Labels = mixedMoment B raw7805step3 raw7805step3Labels := by
      have ha : raw7805step3 = (fun i j => raw7805step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7805step3 raw7805step2; decide +kernel
      have hl : raw7805step3Labels = raw7805step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7805step2 raw7805step2Labels permutation3 permutation2
    _ = mixedMoment B node2783 node2783Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7957 raw7957Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw7957 raw7957Labels = mixedMoment B raw7957step0 raw7957step0Labels := by
      have hz : ∀ j, raw7957 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7957step0 = (fun i j => raw7957 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7957step0 raw7957; decide +kernel
      have hl : raw7957step0Labels = raw7957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7957 raw7957Labels permutation265 hz
    mixedMoment B raw7957step0 raw7957step0Labels = mixedMoment B raw7957step1 raw7957step1Labels := by
      have ha : raw7957step1 = (fun i j => raw7957step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7957step1 raw7957step0; decide +kernel
      have hl : raw7957step1Labels = raw7957step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7957step0 raw7957step0Labels permutation38 permutation2
    mixedMoment B raw7957step1 raw7957step1Labels = mixedMoment B raw7957step2 raw7957step2Labels := by
      have ha : raw7957step2 = -raw7957step1 := by apply Matrix.ext; change ∀ i j, raw7957step2 i j = -(raw7957step1 i j); unfold raw7957step2 raw7957step1; decide +kernel
      have hl : raw7957step2Labels = raw7957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical7958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7958 raw7958Labels = mixedMoment B node3635 node3635Labels := by
  calc
    mixedMoment B raw7958 raw7958Labels = mixedMoment B raw7958step0 raw7958step0Labels := by
      have hz : ∀ j, raw7958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7958step0 = (fun i j => raw7958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7958step0 raw7958; decide +kernel
      have hl : raw7958step0Labels = raw7958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7958 raw7958Labels permutation434 hz
    mixedMoment B raw7958step0 raw7958step0Labels = mixedMoment B raw7958step1 raw7958step1Labels := by
      have hz : ∀ j, raw7958step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7958step1 = (fun i j => raw7958step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7958step1 raw7958step0; decide +kernel
      have hl : raw7958step1Labels = raw7958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7958step0 raw7958step0Labels permutation80 hz
    mixedMoment B raw7958step1 raw7958step1Labels = mixedMoment B raw7958step2 raw7958step2Labels := by
      have hz : ∀ j, raw7958step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7958step2 = (fun i j => raw7958step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7958step2 raw7958step1; decide +kernel
      have hl : raw7958step2Labels = raw7958step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7958step1 raw7958step1Labels permutation14 hz
    mixedMoment B raw7958step2 raw7958step2Labels = mixedMoment B raw7958step3 raw7958step3Labels := by
      have ha : raw7958step3 = -raw7958step2 := by apply Matrix.ext; change ∀ i j, raw7958step3 i j = -(raw7958step2 i j); unfold raw7958step3 raw7958step2; decide +kernel
      have hl : raw7958step3Labels = raw7958step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3635 node3635Labels := by rfl

theorem canonical7959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7959 raw7959Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7959 raw7959Labels = mixedMoment B raw7959step0 raw7959step0Labels := by
      have hz : ∀ j, raw7959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7959step0 = (fun i j => raw7959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7959step0 raw7959; decide +kernel
      have hl : raw7959step0Labels = raw7959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959 raw7959Labels permutation346 hz
    mixedMoment B raw7959step0 raw7959step0Labels = mixedMoment B raw7959step1 raw7959step1Labels := by
      have hz : ∀ j, raw7959step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7959step1 = (fun i j => raw7959step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7959step1 raw7959step0; decide +kernel
      have hl : raw7959step1Labels = raw7959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959step0 raw7959step0Labels permutation56 hz
    mixedMoment B raw7959step1 raw7959step1Labels = mixedMoment B raw7959step2 raw7959step2Labels := by
      have ha : raw7959step2 = (fun i j => raw7959step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7959step2 raw7959step1; decide +kernel
      have hl : raw7959step2Labels = raw7959step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7959step1 raw7959step1Labels permutation9 permutation2
    mixedMoment B raw7959step2 raw7959step2Labels = mixedMoment B raw7959step3 raw7959step3Labels := by
      have ha : raw7959step3 = -raw7959step2 := by apply Matrix.ext; change ∀ i j, raw7959step3 i j = -(raw7959step2 i j); unfold raw7959step3 raw7959step2; decide +kernel
      have hl : raw7959step3Labels = raw7959step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical7960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7960 raw7960Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw7960 raw7960Labels = mixedMoment B raw7960step0 raw7960step0Labels := by
      have hz : ∀ j, raw7960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7960step0 = (fun i j => raw7960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7960step0 raw7960; decide +kernel
      have hl : raw7960step0Labels = raw7960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7960 raw7960Labels permutation346 hz
    mixedMoment B raw7960step0 raw7960step0Labels = mixedMoment B raw7960step1 raw7960step1Labels := by
      have hz : ∀ j, raw7960step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7960step1 = (fun i j => raw7960step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7960step1 raw7960step0; decide +kernel
      have hl : raw7960step1Labels = raw7960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7960step0 raw7960step0Labels permutation56 hz
    mixedMoment B raw7960step1 raw7960step1Labels = mixedMoment B raw7960step2 raw7960step2Labels := by
      have ha : raw7960step2 = -raw7960step1 := by apply Matrix.ext; change ∀ i j, raw7960step2 i j = -(raw7960step1 i j); unfold raw7960step2 raw7960step1; decide +kernel
      have hl : raw7960step2Labels = raw7960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical7961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7961 raw7961Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw7961 raw7961Labels = mixedMoment B raw7961step0 raw7961step0Labels := by
      have hz : ∀ j, raw7961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7961step0 = (fun i j => raw7961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7961step0 raw7961; decide +kernel
      have hl : raw7961step0Labels = raw7961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7961 raw7961Labels permutation346 hz
    mixedMoment B raw7961step0 raw7961step0Labels = mixedMoment B raw7961step1 raw7961step1Labels := by
      have hz : ∀ j, raw7961step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7961step1 = (fun i j => raw7961step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7961step1 raw7961step0; decide +kernel
      have hl : raw7961step1Labels = raw7961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7961step0 raw7961step0Labels permutation56 hz
    mixedMoment B raw7961step1 raw7961step1Labels = mixedMoment B raw7961step2 raw7961step2Labels := by
      have ha : raw7961step2 = (fun i j => raw7961step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7961step2 raw7961step1; decide +kernel
      have hl : raw7961step2Labels = raw7961step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7961step1 raw7961step1Labels permutation8 permutation4
    mixedMoment B raw7961step2 raw7961step2Labels = mixedMoment B raw7961step3 raw7961step3Labels := by
      have ha : raw7961step3 = -raw7961step2 := by apply Matrix.ext; change ∀ i j, raw7961step3 i j = -(raw7961step2 i j); unfold raw7961step3 raw7961step2; decide +kernel
      have hl : raw7961step3Labels = raw7961step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2291 node2291Labels := by rfl

theorem canonical7962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7962 raw7962Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw7962 raw7962Labels = mixedMoment B raw7962step0 raw7962step0Labels := by
      have hz : ∀ j, raw7962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7962step0 = (fun i j => raw7962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7962step0 raw7962; decide +kernel
      have hl : raw7962step0Labels = raw7962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7962 raw7962Labels permutation346 hz
    mixedMoment B raw7962step0 raw7962step0Labels = mixedMoment B raw7962step1 raw7962step1Labels := by
      have hz : ∀ j, raw7962step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7962step1 = (fun i j => raw7962step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7962step1 raw7962step0; decide +kernel
      have hl : raw7962step1Labels = raw7962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7962step0 raw7962step0Labels permutation56 hz
    mixedMoment B raw7962step1 raw7962step1Labels = mixedMoment B raw7962step2 raw7962step2Labels := by
      have ha : raw7962step2 = (fun i j => raw7962step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7962step2 raw7962step1; decide +kernel
      have hl : raw7962step2Labels = raw7962step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7962step1 raw7962step1Labels permutation10 permutation4
    mixedMoment B raw7962step2 raw7962step2Labels = mixedMoment B raw7962step3 raw7962step3Labels := by
      have ha : raw7962step3 = -raw7962step2 := by apply Matrix.ext; change ∀ i j, raw7962step3 i j = -(raw7962step2 i j); unfold raw7962step3 raw7962step2; decide +kernel
      have hl : raw7962step3Labels = raw7962step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

theorem canonical7963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7963 raw7963Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw7963 raw7963Labels = mixedMoment B raw7963step0 raw7963step0Labels := by
      have hz : ∀ j, raw7963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7963step0 = (fun i j => raw7963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7963step0 raw7963; decide +kernel
      have hl : raw7963step0Labels = raw7963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7963 raw7963Labels permutation434 hz
    mixedMoment B raw7963step0 raw7963step0Labels = mixedMoment B raw7963step1 raw7963step1Labels := by
      have hz : ∀ j, raw7963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7963step1 = (fun i j => raw7963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7963step1 raw7963step0; decide +kernel
      have hl : raw7963step1Labels = raw7963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7963step0 raw7963step0Labels permutation80 hz
    mixedMoment B raw7963step1 raw7963step1Labels = mixedMoment B raw7963step2 raw7963step2Labels := by
      have ha : raw7963step2 = (fun i j => raw7963step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7963step2 raw7963step1; decide +kernel
      have hl : raw7963step2Labels = raw7963step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7963step1 raw7963step1Labels permutation10 permutation4
    mixedMoment B raw7963step2 raw7963step2Labels = mixedMoment B raw7963step3 raw7963step3Labels := by
      have ha : raw7963step3 = -raw7963step2 := by apply Matrix.ext; change ∀ i j, raw7963step3 i j = -(raw7963step2 i j); unfold raw7963step3 raw7963step2; decide +kernel
      have hl : raw7963step3Labels = raw7963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

theorem canonical7964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7964 raw7964Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw7964 raw7964Labels = mixedMoment B raw7964step0 raw7964step0Labels := by
      have hz : ∀ j, raw7964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7964step0 = (fun i j => raw7964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7964step0 raw7964; decide +kernel
      have hl : raw7964step0Labels = raw7964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7964 raw7964Labels permutation434 hz
    mixedMoment B raw7964step0 raw7964step0Labels = mixedMoment B raw7964step1 raw7964step1Labels := by
      have hz : ∀ j, raw7964step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7964step1 = (fun i j => raw7964step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7964step1 raw7964step0; decide +kernel
      have hl : raw7964step1Labels = raw7964step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7964step0 raw7964step0Labels permutation80 hz
    mixedMoment B raw7964step1 raw7964step1Labels = mixedMoment B raw7964step2 raw7964step2Labels := by
      have hz : ∀ j, raw7964step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7964step2 = (fun i j => raw7964step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7964step2 raw7964step1; decide +kernel
      have hl : raw7964step2Labels = raw7964step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7964step1 raw7964step1Labels permutation14 hz
    mixedMoment B raw7964step2 raw7964step2Labels = mixedMoment B raw7964step3 raw7964step3Labels := by
      have ha : raw7964step3 = (fun i j => raw7964step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7964step3 raw7964step2; decide +kernel
      have hl : raw7964step3Labels = raw7964step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7964step2 raw7964step2Labels permutation2 permutation4
    mixedMoment B raw7964step3 raw7964step3Labels = mixedMoment B raw7964step4 raw7964step4Labels := by
      have ha : raw7964step4 = -raw7964step3 := by apply Matrix.ext; change ∀ i j, raw7964step4 i j = -(raw7964step3 i j); unfold raw7964step4 raw7964step3; decide +kernel
      have hl : raw7964step4Labels = raw7964step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3629 node3629Labels := by rfl

theorem canonical7965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7965 raw7965Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7965 raw7965Labels = mixedMoment B raw7965step0 raw7965step0Labels := by
      have hz : ∀ j, raw7965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7965step0 = (fun i j => raw7965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7965step0 raw7965; decide +kernel
      have hl : raw7965step0Labels = raw7965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7965 raw7965Labels permutation346 hz
    mixedMoment B raw7965step0 raw7965step0Labels = mixedMoment B raw7965step1 raw7965step1Labels := by
      have ha : raw7965step1 = (fun i j => raw7965step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7965step1 raw7965step0; decide +kernel
      have hl : raw7965step1Labels = raw7965step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7965step0 raw7965step0Labels permutation44 permutation4
    mixedMoment B raw7965step1 raw7965step1Labels = mixedMoment B raw7965step2 raw7965step2Labels := by
      have ha : raw7965step2 = -raw7965step1 := by apply Matrix.ext; change ∀ i j, raw7965step2 i j = -(raw7965step1 i j); unfold raw7965step2 raw7965step1; decide +kernel
      have hl : raw7965step2Labels = raw7965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical7966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7966 raw7966Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7966 raw7966Labels = mixedMoment B raw7966step0 raw7966step0Labels := by
      have hz : ∀ j, raw7966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7966step0 = (fun i j => raw7966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7966step0 raw7966; decide +kernel
      have hl : raw7966step0Labels = raw7966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966 raw7966Labels permutation346 hz
    mixedMoment B raw7966step0 raw7966step0Labels = mixedMoment B raw7966step1 raw7966step1Labels := by
      have hz : ∀ j, raw7966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7966step1 = (fun i j => raw7966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7966step1 raw7966step0; decide +kernel
      have hl : raw7966step1Labels = raw7966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966step0 raw7966step0Labels permutation56 hz
    mixedMoment B raw7966step1 raw7966step1Labels = mixedMoment B raw7966step2 raw7966step2Labels := by
      have ha : raw7966step2 = (fun i j => raw7966step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7966step2 raw7966step1; decide +kernel
      have hl : raw7966step2Labels = raw7966step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7966step1 raw7966step1Labels permutation10 permutation4
    mixedMoment B raw7966step2 raw7966step2Labels = mixedMoment B raw7966step3 raw7966step3Labels := by
      have ha : raw7966step3 = -raw7966step2 := by apply Matrix.ext; change ∀ i j, raw7966step3 i j = -(raw7966step2 i j); unfold raw7966step3 raw7966step2; decide +kernel
      have hl : raw7966step3Labels = raw7966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical7967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7967 raw7967Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw7967 raw7967Labels = mixedMoment B raw7967step0 raw7967step0Labels := by
      have hz : ∀ j, raw7967 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7967step0 = (fun i j => raw7967 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7967step0 raw7967; decide +kernel
      have hl : raw7967step0Labels = raw7967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7967 raw7967Labels permutation265 hz
    mixedMoment B raw7967step0 raw7967step0Labels = mixedMoment B raw7967step1 raw7967step1Labels := by
      have ha : raw7967step1 = (fun i j => raw7967step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7967step1 raw7967step0; decide +kernel
      have hl : raw7967step1Labels = raw7967step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7967step0 raw7967step0Labels permutation34 permutation4
    mixedMoment B raw7967step1 raw7967step1Labels = mixedMoment B raw7967step2 raw7967step2Labels := by
      have ha : raw7967step2 = -raw7967step1 := by apply Matrix.ext; change ∀ i j, raw7967step2 i j = -(raw7967step1 i j); unfold raw7967step2 raw7967step1; decide +kernel
      have hl : raw7967step2Labels = raw7967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1014 node1014Labels = Sparse.eval nodeValue1014 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1014) = mixedMoment B node1014 node1014Labels := rfl
  simpa [nodeValue1014, Sparse.eval] using hc.symm

theorem sound1015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1015 node1015Labels = Sparse.eval nodeValue1015 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1015) = mixedMoment B node1015 node1015Labels := rfl
  simpa [nodeValue1015, Sparse.eval] using hc.symm

theorem sound1021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1021 node1021Labels = Sparse.eval nodeValue1021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1021) = mixedMoment B node1021 node1021Labels := rfl
  simpa [nodeValue1021, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1030 node1030Labels = Sparse.eval nodeValue1030 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1030) = mixedMoment B node1030 node1030Labels := rfl
  simpa [nodeValue1030, Sparse.eval] using hc.symm

theorem sound1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1042 node1042Labels = Sparse.eval nodeValue1042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1042) = mixedMoment B node1042 node1042Labels := rfl
  simpa [nodeValue1042, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1310 node1310Labels = Sparse.eval nodeValue1310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1310) = mixedMoment B node1310 node1310Labels := rfl
  simpa [nodeValue1310, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1463 node1463Labels = Sparse.eval nodeValue1463 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1463) = mixedMoment B node1463 node1463Labels := rfl
  simpa [nodeValue1463, Sparse.eval] using hc.symm

theorem sound1465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1465 node1465Labels = Sparse.eval nodeValue1465 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1465) = mixedMoment B node1465 node1465Labels := rfl
  simpa [nodeValue1465, Sparse.eval] using hc.symm

theorem sound1466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1466 node1466Labels = Sparse.eval nodeValue1466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1466) = mixedMoment B node1466 node1466Labels := rfl
  simpa [nodeValue1466, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2014 node2014Labels = Sparse.eval nodeValue2014 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2014) = mixedMoment B node2014 node2014Labels := rfl
  simpa [nodeValue2014, Sparse.eval] using hc.symm

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2083 node2083Labels = Sparse.eval nodeValue2083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2083) = mixedMoment B node2083 node2083Labels := rfl
  simpa [nodeValue2083, Sparse.eval] using hc.symm

theorem sound2084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2084 node2084Labels = Sparse.eval nodeValue2084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2084) = mixedMoment B node2084 node2084Labels := rfl
  simpa [nodeValue2084, Sparse.eval] using hc.symm

theorem sound2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2089 node2089Labels = Sparse.eval nodeValue2089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2089) = mixedMoment B node2089 node2089Labels := rfl
  simpa [nodeValue2089, Sparse.eval] using hc.symm

theorem sound2097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2097 node2097Labels = Sparse.eval nodeValue2097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2097) = mixedMoment B node2097 node2097Labels := rfl
  simpa [nodeValue2097, Sparse.eval] using hc.symm

theorem sound2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2108 node2108Labels = Sparse.eval nodeValue2108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2108) = mixedMoment B node2108 node2108Labels := rfl
  simpa [nodeValue2108, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2124 node2124Labels = Sparse.eval nodeValue2124 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2124) = mixedMoment B node2124 node2124Labels := rfl
  simpa [nodeValue2124, Sparse.eval] using hc.symm

theorem sound2125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2125 node2125Labels = Sparse.eval nodeValue2125 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2125) = mixedMoment B node2125 node2125Labels := rfl
  simpa [nodeValue2125, Sparse.eval] using hc.symm

theorem sound2126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2126 node2126Labels = Sparse.eval nodeValue2126 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2126) = mixedMoment B node2126 node2126Labels := rfl
  simpa [nodeValue2126, Sparse.eval] using hc.symm

theorem sound2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2133 node2133Labels = Sparse.eval nodeValue2133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2133) = mixedMoment B node2133 node2133Labels := rfl
  simpa [nodeValue2133, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2233 node2233Labels = Sparse.eval nodeValue2233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2233) = mixedMoment B node2233 node2233Labels := rfl
  simpa [nodeValue2233, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = 0 := by
  exact mixedMoment_order_one B hB node2264 node2264Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = 0 := by
  exact mixedMoment_order_one B hB node2291 node2291Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2243 node2243Labels = Sparse.eval nodeValue2243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2243) = mixedMoment B node2243 node2243Labels := rfl
  simpa [nodeValue2243, Sparse.eval] using hc.symm

theorem sound2245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2245 node2245Labels = Sparse.eval nodeValue2245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2245) = mixedMoment B node2245 node2245Labels := rfl
  simpa [nodeValue2245, Sparse.eval] using hc.symm

theorem sound2253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2253 node2253Labels = Sparse.eval nodeValue2253 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2253) = mixedMoment B node2253 node2253Labels := rfl
  simpa [nodeValue2253, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2264 node2264Labels = Sparse.eval nodeValue2264 (mixedVector B) := by
  simpa only [nodeValue2264, Sparse.eval_nil] using zero2264 B _hB _hF

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

theorem sound2291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2291 node2291Labels = Sparse.eval nodeValue2291 (mixedVector B) := by
  simpa only [nodeValue2291, Sparse.eval_nil] using zero2291 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2474 node2474Labels = Sparse.eval nodeValue2474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2474) = mixedMoment B node2474 node2474Labels := rfl
  simpa [nodeValue2474, Sparse.eval] using hc.symm

theorem sound2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2486 node2486Labels = Sparse.eval nodeValue2486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2486) = mixedMoment B node2486 node2486Labels := rfl
  simpa [nodeValue2486, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2497 node2497Labels = Sparse.eval nodeValue2497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2497) = mixedMoment B node2497 node2497Labels := rfl
  simpa [nodeValue2497, Sparse.eval] using hc.symm

theorem sound2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2513 node2513Labels = Sparse.eval nodeValue2513 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2513) = mixedMoment B node2513 node2513Labels := rfl
  simpa [nodeValue2513, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2603 node2603Labels = Sparse.eval nodeValue2603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2603) = mixedMoment B node2603 node2603Labels := rfl
  simpa [nodeValue2603, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2716 node2716Labels = Sparse.eval nodeValue2716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2716) = mixedMoment B node2716 node2716Labels := rfl
  simpa [nodeValue2716, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

theorem sound2789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2789 node2789Labels = Sparse.eval nodeValue2789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2789) = mixedMoment B node2789 node2789Labels := rfl
  simpa [nodeValue2789, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3170 node3170Labels = Sparse.eval nodeValue3170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3170) = mixedMoment B node3170 node3170Labels := rfl
  simpa [nodeValue3170, Sparse.eval] using hc.symm

theorem sound3174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3174 node3174Labels = Sparse.eval nodeValue3174 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3174) = mixedMoment B node3174 node3174Labels := rfl
  simpa [nodeValue3174, Sparse.eval] using hc.symm

theorem sound3180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3180 node3180Labels = Sparse.eval nodeValue3180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3180) = mixedMoment B node3180 node3180Labels := rfl
  simpa [nodeValue3180, Sparse.eval] using hc.symm

theorem sound3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3196 node3196Labels = Sparse.eval nodeValue3196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3196) = mixedMoment B node3196 node3196Labels := rfl
  simpa [nodeValue3196, Sparse.eval] using hc.symm

theorem sound3198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3198 node3198Labels = Sparse.eval nodeValue3198 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3198) = mixedMoment B node3198 node3198Labels := rfl
  simpa [nodeValue3198, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3217 node3217Labels = Sparse.eval nodeValue3217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3217) = mixedMoment B node3217 node3217Labels := rfl
  simpa [nodeValue3217, Sparse.eval] using hc.symm

theorem sound3222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3222 node3222Labels = Sparse.eval nodeValue3222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3222) = mixedMoment B node3222 node3222Labels := rfl
  simpa [nodeValue3222, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3547 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = 0 := by
  exact mixedMoment_order_one B hB node3547 node3547Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

theorem sound3547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3547 node3547Labels = Sparse.eval nodeValue3547 (mixedVector B) := by
  simpa only [nodeValue3547, Sparse.eval_nil] using zero3547 B _hB _hF

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3567 node3567Labels = Sparse.eval nodeValue3567 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3567) = mixedMoment B node3567 node3567Labels := rfl
  simpa [nodeValue3567, Sparse.eval] using hc.symm

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3618 node3618Labels = 0 := by
  exact mixedMoment_alpha B hF node3618 node3618Labels 1 permutation434
    (by decide +kernel)

theorem zero3629 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3629 node3629Labels = 0 := by
  exact mixedMoment_order_one B hB node3629 node3629Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero3635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3635 node3635Labels = 0 := by
  exact mixedMoment_order_one B hB node3635 node3635Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

theorem sound3618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3618 node3618Labels = Sparse.eval nodeValue3618 (mixedVector B) := by
  simpa only [nodeValue3618, Sparse.eval_nil] using zero3618 B _hB _hF

theorem sound3619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3619 node3619Labels = Sparse.eval nodeValue3619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3619) = mixedMoment B node3619 node3619Labels := rfl
  simpa [nodeValue3619, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

theorem sound3629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3629 node3629Labels = Sparse.eval nodeValue3629 (mixedVector B) := by
  simpa only [nodeValue3629, Sparse.eval_nil] using zero3629 B _hB _hF

theorem sound3635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3635 node3635Labels = Sparse.eval nodeValue3635 (mixedVector B) := by
  simpa only [nodeValue3635, Sparse.eval_nil] using zero3635 B _hB _hF

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3803 node3803Labels = Sparse.eval nodeValue3803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3803) = mixedMoment B node3803 node3803Labels := rfl
  simpa [nodeValue3803, Sparse.eval] using hc.symm

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources13
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm420 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA420 + difference 4 0) (sourceB420 + difference 0 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA420 + difference 4 0) (sourceB420 + difference 0 4) sourceC420) = raw7795 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7795; decide +kernel
    rw [ha]
    exact (canonical7795 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA420 + difference 4 1) (sourceB420 + difference 1 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA420 + difference 4 1) (sourceB420 + difference 1 4) sourceC420) = raw7802 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7802; decide +kernel
    rw [ha]
    exact (canonical7802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA420 + difference 4 2) (sourceB420 + difference 2 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA420 + difference 4 2) (sourceB420 + difference 2 4) sourceC420) = raw7803 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7803; decide +kernel
    rw [ha]
    exact (canonical7803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA420 + difference 4 3) (sourceB420 + difference 3 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA420 + difference 4 3) (sourceB420 + difference 3 4) sourceC420) = raw7804 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7804; decide +kernel
    rw [ha]
    exact (canonical7804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA420 + difference 4 4) (sourceB420 + difference 4 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA420 + difference 4 4) (sourceB420 + difference 4 4) sourceC420) = raw7791 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7791; decide +kernel
    rw [ha]
    exact (canonical7791 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA420 + difference 4 5) (sourceB420 + difference 5 4) sourceC420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA420 + difference 4 5) (sourceB420 + difference 5 4) sourceC420) = raw7805 := by
      apply Matrix.ext; unfold tripleCharges sourceA420 sourceB420 sourceC420 difference raw7805; decide +kernel
    rw [ha]
    exact (canonical7805 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA420 + sourceB420) sourceC420) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA420 + sourceB420) sourceC420) = raw7797 := by
      apply Matrix.ext; unfold doubleCharges sourceA420 sourceB420 sourceC420 raw7797; decide +kernel
    rw [ha]
    exact (canonical7797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA420 sourceB420 sourceC420
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm420, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm428 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA428 + difference 0 0) (sourceB428 + difference 0 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA428 + difference 0 0) (sourceB428 + difference 0 0) sourceC428) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA428 + difference 0 1) (sourceB428 + difference 1 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA428 + difference 0 1) (sourceB428 + difference 1 0) sourceC428) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA428 + difference 0 2) (sourceB428 + difference 2 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA428 + difference 0 2) (sourceB428 + difference 2 0) sourceC428) = raw7957 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7957; decide +kernel
    rw [ha]
    exact (canonical7957 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA428 + difference 0 3) (sourceB428 + difference 3 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA428 + difference 0 3) (sourceB428 + difference 3 0) sourceC428) = raw7958 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7958; decide +kernel
    rw [ha]
    exact (canonical7958 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA428 + difference 0 4) (sourceB428 + difference 4 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA428 + difference 0 4) (sourceB428 + difference 4 0) sourceC428) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA428 + difference 0 5) (sourceB428 + difference 5 0) sourceC428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA428 + difference 0 5) (sourceB428 + difference 5 0) sourceC428) = raw7960 := by
      apply Matrix.ext; unfold tripleCharges sourceA428 sourceB428 sourceC428 difference raw7960; decide +kernel
    rw [ha]
    exact (canonical7960 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA428 + sourceB428) sourceC428) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA428 + sourceB428) sourceC428) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA428 sourceB428 sourceC428 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA428 sourceB428 sourceC428
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm428, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm429 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA429 + difference 0 0) (sourceB429 + difference 0 0) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA429 + difference 0 0) (sourceB429 + difference 0 0) sourceC429) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA429 + difference 1 0) (sourceB429 + difference 0 1) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA429 + difference 1 0) (sourceB429 + difference 0 1) sourceC429) = raw5769 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw5769; decide +kernel
    rw [ha]
    exact (canonical5769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA429 + difference 2 0) (sourceB429 + difference 0 2) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA429 + difference 2 0) (sourceB429 + difference 0 2) sourceC429) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA429 + difference 3 0) (sourceB429 + difference 0 3) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA429 + difference 3 0) (sourceB429 + difference 0 3) sourceC429) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA429 + difference 4 0) (sourceB429 + difference 0 4) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA429 + difference 4 0) (sourceB429 + difference 0 4) sourceC429) = raw7961 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw7961; decide +kernel
    rw [ha]
    exact (canonical7961 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA429 + difference 5 0) (sourceB429 + difference 0 5) sourceC429) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA429 + difference 5 0) (sourceB429 + difference 0 5) sourceC429) = raw7962 := by
      apply Matrix.ext; unfold tripleCharges sourceA429 sourceB429 sourceC429 difference raw7962; decide +kernel
    rw [ha]
    exact (canonical7962 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA429 + sourceB429) sourceC429) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA429 + sourceB429) sourceC429) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA429 sourceB429 sourceC429 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA429 sourceB429 sourceC429
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm429, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm430 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA430 + difference 0 3) (sourceB430 + difference 3 0) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA430 + difference 0 3) (sourceB430 + difference 3 0) sourceC430) = raw7958 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7958; decide +kernel
    rw [ha]
    exact (canonical7958 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA430 + difference 1 3) (sourceB430 + difference 3 1) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA430 + difference 1 3) (sourceB430 + difference 3 1) sourceC430) = raw7963 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7963; decide +kernel
    rw [ha]
    exact (canonical7963 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA430 + difference 2 3) (sourceB430 + difference 3 2) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA430 + difference 2 3) (sourceB430 + difference 3 2) sourceC430) = raw7282 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7282; decide +kernel
    rw [ha]
    exact (canonical7282 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA430 + difference 3 3) (sourceB430 + difference 3 3) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA430 + difference 3 3) (sourceB430 + difference 3 3) sourceC430) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA430 + difference 4 3) (sourceB430 + difference 3 4) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA430 + difference 4 3) (sourceB430 + difference 3 4) sourceC430) = raw7697 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7697; decide +kernel
    rw [ha]
    exact (canonical7697 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA430 + difference 5 3) (sourceB430 + difference 3 5) sourceC430) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA430 + difference 5 3) (sourceB430 + difference 3 5) sourceC430) = raw7964 := by
      apply Matrix.ext; unfold tripleCharges sourceA430 sourceB430 sourceC430 difference raw7964; decide +kernel
    rw [ha]
    exact (canonical7964 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA430 + sourceB430) sourceC430) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA430 + sourceB430) sourceC430) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA430 sourceB430 sourceC430 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA430 sourceB430 sourceC430
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm430, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm431 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA431 + difference 0 4) (sourceB431 + difference 4 0) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA431 + difference 0 4) (sourceB431 + difference 4 0) sourceC431) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA431 + difference 1 4) (sourceB431 + difference 4 1) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA431 + difference 1 4) (sourceB431 + difference 4 1) sourceC431) = raw7965 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7965; decide +kernel
    rw [ha]
    exact (canonical7965 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA431 + difference 2 4) (sourceB431 + difference 4 2) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA431 + difference 2 4) (sourceB431 + difference 4 2) sourceC431) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA431 + difference 3 4) (sourceB431 + difference 4 3) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA431 + difference 3 4) (sourceB431 + difference 4 3) sourceC431) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA431 + difference 4 4) (sourceB431 + difference 4 4) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA431 + difference 4 4) (sourceB431 + difference 4 4) sourceC431) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA431 + difference 5 4) (sourceB431 + difference 4 5) sourceC431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA431 + difference 5 4) (sourceB431 + difference 4 5) sourceC431) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA431 sourceB431 sourceC431 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA431 + sourceB431) sourceC431) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA431 + sourceB431) sourceC431) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA431 sourceB431 sourceC431 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA431 sourceB431 sourceC431
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm431, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm432 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA432 + difference 5 0) (sourceB432 + difference 0 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA432 + difference 5 0) (sourceB432 + difference 0 5) sourceC432) = raw7962 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7962; decide +kernel
    rw [ha]
    exact (canonical7962 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA432 + difference 5 1) (sourceB432 + difference 1 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA432 + difference 5 1) (sourceB432 + difference 1 5) sourceC432) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA432 + difference 5 2) (sourceB432 + difference 2 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA432 + difference 5 2) (sourceB432 + difference 2 5) sourceC432) = raw7967 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7967; decide +kernel
    rw [ha]
    exact (canonical7967 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA432 + difference 5 3) (sourceB432 + difference 3 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA432 + difference 5 3) (sourceB432 + difference 3 5) sourceC432) = raw7964 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7964; decide +kernel
    rw [ha]
    exact (canonical7964 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA432 + difference 5 4) (sourceB432 + difference 4 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA432 + difference 5 4) (sourceB432 + difference 4 5) sourceC432) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA432 + difference 5 5) (sourceB432 + difference 5 5) sourceC432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA432 + difference 5 5) (sourceB432 + difference 5 5) sourceC432) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA432 sourceB432 sourceC432 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA432 + sourceB432) sourceC432) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA432 + sourceB432) sourceC432) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA432 sourceB432 sourceC432 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA432 sourceB432 sourceC432
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm432, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources5
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm182 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA182 + difference 3 0) (sourceB182 + difference 0 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA182 + difference 3 0) (sourceB182 + difference 0 3) sourceC182) = raw5317 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5317; decide +kernel
    rw [ha]
    exact (canonical5317 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA182 + difference 3 1) (sourceB182 + difference 1 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA182 + difference 3 1) (sourceB182 + difference 1 3) sourceC182) = raw5325 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5325; decide +kernel
    rw [ha]
    exact (canonical5325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA182 + difference 3 2) (sourceB182 + difference 2 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA182 + difference 3 2) (sourceB182 + difference 2 3) sourceC182) = raw5331 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5331; decide +kernel
    rw [ha]
    exact (canonical5331 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA182 + difference 3 3) (sourceB182 + difference 3 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA182 + difference 3 3) (sourceB182 + difference 3 3) sourceC182) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA182 + difference 3 4) (sourceB182 + difference 4 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA182 + difference 3 4) (sourceB182 + difference 4 3) sourceC182) = raw5334 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5334; decide +kernel
    rw [ha]
    exact (canonical5334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA182 + difference 3 5) (sourceB182 + difference 5 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA182 + difference 3 5) (sourceB182 + difference 5 3) sourceC182) = raw5335 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5335; decide +kernel
    rw [ha]
    exact (canonical5335 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA182 + sourceB182) sourceC182) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA182 + sourceB182) sourceC182) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA182 sourceB182 sourceC182 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA182 sourceB182 sourceC182
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm182, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm183 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA183 + difference 0 3) (sourceB183 + difference 3 0) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA183 + difference 0 3) (sourceB183 + difference 3 0) sourceC183) = raw5311 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5311; decide +kernel
    rw [ha]
    exact (canonical5311 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA183 + difference 1 3) (sourceB183 + difference 3 1) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2124) := by
    have ha : (tripleCharges (sourceA183 + difference 1 3) (sourceB183 + difference 3 1) sourceC183) = raw5321 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5321; decide +kernel
    rw [ha]
    exact (canonical5321 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA183 + difference 2 3) (sourceB183 + difference 3 2) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA183 + difference 2 3) (sourceB183 + difference 3 2) sourceC183) = raw5328 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5328; decide +kernel
    rw [ha]
    exact (canonical5328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA183 + difference 3 3) (sourceB183 + difference 3 3) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA183 + difference 3 3) (sourceB183 + difference 3 3) sourceC183) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA183 + difference 4 3) (sourceB183 + difference 3 4) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2126) := by
    have ha : (tripleCharges (sourceA183 + difference 4 3) (sourceB183 + difference 3 4) sourceC183) = raw5336 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5336; decide +kernel
    rw [ha]
    exact (canonical5336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA183 + difference 5 3) (sourceB183 + difference 3 5) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA183 + difference 5 3) (sourceB183 + difference 3 5) sourceC183) = raw5337 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5337; decide +kernel
    rw [ha]
    exact (canonical5337 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA183 + sourceB183) sourceC183) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA183 + sourceB183) sourceC183) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA183 sourceB183 sourceC183 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA183 sourceB183 sourceC183
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm183, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm184 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA184 + difference 4 0) (sourceB184 + difference 0 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1030) := by
    have ha : (tripleCharges (sourceA184 + difference 4 0) (sourceB184 + difference 0 4) sourceC184) = raw5318 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5318; decide +kernel
    rw [ha]
    exact (canonical5318 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA184 + difference 4 1) (sourceB184 + difference 1 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2014) := by
    have ha : (tripleCharges (sourceA184 + difference 4 1) (sourceB184 + difference 1 4) sourceC184) = raw5326 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5326; decide +kernel
    rw [ha]
    exact (canonical5326 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA184 + difference 4 2) (sourceB184 + difference 2 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2097) := by
    have ha : (tripleCharges (sourceA184 + difference 4 2) (sourceB184 + difference 2 4) sourceC184) = raw5332 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5332; decide +kernel
    rw [ha]
    exact (canonical5332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA184 + difference 4 3) (sourceB184 + difference 3 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2126) := by
    have ha : (tripleCharges (sourceA184 + difference 4 3) (sourceB184 + difference 3 4) sourceC184) = raw5336 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5336; decide +kernel
    rw [ha]
    exact (canonical5336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA184 + difference 4 4) (sourceB184 + difference 4 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA184 + difference 4 4) (sourceB184 + difference 4 4) sourceC184) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA184 + difference 4 5) (sourceB184 + difference 5 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA184 + difference 4 5) (sourceB184 + difference 5 4) sourceC184) = raw5338 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5338; decide +kernel
    rw [ha]
    exact (canonical5338 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA184 + sourceB184) sourceC184) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA184 + sourceB184) sourceC184) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA184 sourceB184 sourceC184 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA184 sourceB184 sourceC184
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm184, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm187 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA187 + difference 0 0) (sourceB187 + difference 0 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA187 + difference 0 0) (sourceB187 + difference 0 0) sourceC187) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA187 + difference 0 1) (sourceB187 + difference 1 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA187 + difference 0 1) (sourceB187 + difference 1 0) sourceC187) = raw5400 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5400; decide +kernel
    rw [ha]
    exact (canonical5400 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA187 + difference 0 2) (sourceB187 + difference 2 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA187 + difference 0 2) (sourceB187 + difference 2 0) sourceC187) = raw5401 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5401; decide +kernel
    rw [ha]
    exact (canonical5401 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA187 + difference 0 3) (sourceB187 + difference 3 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA187 + difference 0 3) (sourceB187 + difference 3 0) sourceC187) = raw5402 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5402; decide +kernel
    rw [ha]
    exact (canonical5402 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA187 + difference 0 4) (sourceB187 + difference 4 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA187 + difference 0 4) (sourceB187 + difference 4 0) sourceC187) = raw5403 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5403; decide +kernel
    rw [ha]
    exact (canonical5403 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA187 + difference 0 5) (sourceB187 + difference 5 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA187 + difference 0 5) (sourceB187 + difference 5 0) sourceC187) = raw5404 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5404; decide +kernel
    rw [ha]
    exact (canonical5404 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA187 + sourceB187) sourceC187) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA187 + sourceB187) sourceC187) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA187 sourceB187 sourceC187 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA187 sourceB187 sourceC187
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm187, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm188 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA188 + difference 0 0) (sourceB188 + difference 0 0) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA188 + difference 0 0) (sourceB188 + difference 0 0) sourceC188) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA188 + difference 1 0) (sourceB188 + difference 0 1) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1463) := by
    have ha : (tripleCharges (sourceA188 + difference 1 0) (sourceB188 + difference 0 1) sourceC188) = raw5406 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5406; decide +kernel
    rw [ha]
    exact (canonical5406 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA188 + difference 2 0) (sourceB188 + difference 0 2) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1466) := by
    have ha : (tripleCharges (sourceA188 + difference 2 0) (sourceB188 + difference 0 2) sourceC188) = raw5407 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5407; decide +kernel
    rw [ha]
    exact (canonical5407 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA188 + difference 3 0) (sourceB188 + difference 0 3) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1465) := by
    have ha : (tripleCharges (sourceA188 + difference 3 0) (sourceB188 + difference 0 3) sourceC188) = raw5408 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5408; decide +kernel
    rw [ha]
    exact (canonical5408 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA188 + difference 4 0) (sourceB188 + difference 0 4) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1466) := by
    have ha : (tripleCharges (sourceA188 + difference 4 0) (sourceB188 + difference 0 4) sourceC188) = raw5409 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5409; decide +kernel
    rw [ha]
    exact (canonical5409 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA188 + difference 5 0) (sourceB188 + difference 0 5) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1465) := by
    have ha : (tripleCharges (sourceA188 + difference 5 0) (sourceB188 + difference 0 5) sourceC188) = raw5410 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5410; decide +kernel
    rw [ha]
    exact (canonical5410 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA188 + sourceB188) sourceC188) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA188 + sourceB188) sourceC188) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA188 sourceB188 sourceC188 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA188 sourceB188 sourceC188
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm188, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm189 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA189 + difference 1 0) (sourceB189 + difference 0 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1463) := by
    have ha : (tripleCharges (sourceA189 + difference 1 0) (sourceB189 + difference 0 1) sourceC189) = raw5406 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5406; decide +kernel
    rw [ha]
    exact (canonical5406 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA189 + difference 1 1) (sourceB189 + difference 1 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA189 + difference 1 1) (sourceB189 + difference 1 1) sourceC189) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA189 + difference 1 2) (sourceB189 + difference 2 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA189 + difference 1 2) (sourceB189 + difference 2 1) sourceC189) = raw5411 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5411; decide +kernel
    rw [ha]
    exact (canonical5411 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA189 + difference 1 3) (sourceB189 + difference 3 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA189 + difference 1 3) (sourceB189 + difference 3 1) sourceC189) = raw5412 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5412; decide +kernel
    rw [ha]
    exact (canonical5412 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA189 + difference 1 4) (sourceB189 + difference 4 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA189 + difference 1 4) (sourceB189 + difference 4 1) sourceC189) = raw5413 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5413; decide +kernel
    rw [ha]
    exact (canonical5413 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA189 + difference 1 5) (sourceB189 + difference 5 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA189 + difference 1 5) (sourceB189 + difference 5 1) sourceC189) = raw5414 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5414; decide +kernel
    rw [ha]
    exact (canonical5414 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA189 + sourceB189) sourceC189) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA189 + sourceB189) sourceC189) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA189 sourceB189 sourceC189 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA189 sourceB189 sourceC189
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm189, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm190 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA190 + difference 0 1) (sourceB190 + difference 1 0) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA190 + difference 0 1) (sourceB190 + difference 1 0) sourceC190) = raw5400 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5400; decide +kernel
    rw [ha]
    exact (canonical5400 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA190 + difference 1 1) (sourceB190 + difference 1 1) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA190 + difference 1 1) (sourceB190 + difference 1 1) sourceC190) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA190 + difference 2 1) (sourceB190 + difference 1 2) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA190 + difference 2 1) (sourceB190 + difference 1 2) sourceC190) = raw5415 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5415; decide +kernel
    rw [ha]
    exact (canonical5415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA190 + difference 3 1) (sourceB190 + difference 1 3) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA190 + difference 3 1) (sourceB190 + difference 1 3) sourceC190) = raw5416 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5416; decide +kernel
    rw [ha]
    exact (canonical5416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA190 + difference 4 1) (sourceB190 + difference 1 4) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA190 + difference 4 1) (sourceB190 + difference 1 4) sourceC190) = raw5417 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5417; decide +kernel
    rw [ha]
    exact (canonical5417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA190 + difference 5 1) (sourceB190 + difference 1 5) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA190 + difference 5 1) (sourceB190 + difference 1 5) sourceC190) = raw5418 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5418; decide +kernel
    rw [ha]
    exact (canonical5418 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA190 + sourceB190) sourceC190) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA190 + sourceB190) sourceC190) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA190 sourceB190 sourceC190 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA190 sourceB190 sourceC190
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm190, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm191 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA191 + difference 2 0) (sourceB191 + difference 0 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1466) := by
    have ha : (tripleCharges (sourceA191 + difference 2 0) (sourceB191 + difference 0 2) sourceC191) = raw5407 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5407; decide +kernel
    rw [ha]
    exact (canonical5407 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA191 + difference 2 1) (sourceB191 + difference 1 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA191 + difference 2 1) (sourceB191 + difference 1 2) sourceC191) = raw5415 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5415; decide +kernel
    rw [ha]
    exact (canonical5415 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA191 + difference 2 2) (sourceB191 + difference 2 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA191 + difference 2 2) (sourceB191 + difference 2 2) sourceC191) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA191 + difference 2 3) (sourceB191 + difference 3 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA191 + difference 2 3) (sourceB191 + difference 3 2) sourceC191) = raw5419 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5419; decide +kernel
    rw [ha]
    exact (canonical5419 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA191 + difference 2 4) (sourceB191 + difference 4 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA191 + difference 2 4) (sourceB191 + difference 4 2) sourceC191) = raw5420 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5420; decide +kernel
    rw [ha]
    exact (canonical5420 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA191 + difference 2 5) (sourceB191 + difference 5 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA191 + difference 2 5) (sourceB191 + difference 5 2) sourceC191) = raw5421 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5421; decide +kernel
    rw [ha]
    exact (canonical5421 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA191 + sourceB191) sourceC191) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA191 + sourceB191) sourceC191) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA191 sourceB191 sourceC191 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA191 sourceB191 sourceC191
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm191, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources6
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm192 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA192 + difference 0 2) (sourceB192 + difference 2 0) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA192 + difference 0 2) (sourceB192 + difference 2 0) sourceC192) = raw5401 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5401; decide +kernel
    rw [ha]
    exact (canonical5401 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA192 + difference 1 2) (sourceB192 + difference 2 1) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA192 + difference 1 2) (sourceB192 + difference 2 1) sourceC192) = raw5411 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5411; decide +kernel
    rw [ha]
    exact (canonical5411 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA192 + difference 2 2) (sourceB192 + difference 2 2) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA192 + difference 2 2) (sourceB192 + difference 2 2) sourceC192) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA192 + difference 3 2) (sourceB192 + difference 2 3) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA192 + difference 3 2) (sourceB192 + difference 2 3) sourceC192) = raw5422 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5422; decide +kernel
    rw [ha]
    exact (canonical5422 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA192 + difference 4 2) (sourceB192 + difference 2 4) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA192 + difference 4 2) (sourceB192 + difference 2 4) sourceC192) = raw5423 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5423; decide +kernel
    rw [ha]
    exact (canonical5423 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA192 + difference 5 2) (sourceB192 + difference 2 5) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA192 + difference 5 2) (sourceB192 + difference 2 5) sourceC192) = raw5424 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5424; decide +kernel
    rw [ha]
    exact (canonical5424 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA192 + sourceB192) sourceC192) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA192 + sourceB192) sourceC192) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA192 sourceB192 sourceC192 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA192 sourceB192 sourceC192
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm192, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm193 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA193 + difference 3 0) (sourceB193 + difference 0 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1465) := by
    have ha : (tripleCharges (sourceA193 + difference 3 0) (sourceB193 + difference 0 3) sourceC193) = raw5408 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5408; decide +kernel
    rw [ha]
    exact (canonical5408 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA193 + difference 3 1) (sourceB193 + difference 1 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA193 + difference 3 1) (sourceB193 + difference 1 3) sourceC193) = raw5416 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5416; decide +kernel
    rw [ha]
    exact (canonical5416 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA193 + difference 3 2) (sourceB193 + difference 2 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA193 + difference 3 2) (sourceB193 + difference 2 3) sourceC193) = raw5422 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5422; decide +kernel
    rw [ha]
    exact (canonical5422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA193 + difference 3 3) (sourceB193 + difference 3 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA193 + difference 3 3) (sourceB193 + difference 3 3) sourceC193) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA193 + difference 3 4) (sourceB193 + difference 4 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA193 + difference 3 4) (sourceB193 + difference 4 3) sourceC193) = raw5425 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5425; decide +kernel
    rw [ha]
    exact (canonical5425 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA193 + difference 3 5) (sourceB193 + difference 5 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA193 + difference 3 5) (sourceB193 + difference 5 3) sourceC193) = raw5426 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5426; decide +kernel
    rw [ha]
    exact (canonical5426 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA193 + sourceB193) sourceC193) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA193 + sourceB193) sourceC193) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA193 sourceB193 sourceC193 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA193 sourceB193 sourceC193
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm193, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm197 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA197 + difference 0 0) (sourceB197 + difference 0 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA197 + difference 0 0) (sourceB197 + difference 0 0) sourceC197) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA197 + difference 0 1) (sourceB197 + difference 1 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA197 + difference 0 1) (sourceB197 + difference 1 0) sourceC197) = raw5518 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5518; decide +kernel
    rw [ha]
    exact (canonical5518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA197 + difference 0 2) (sourceB197 + difference 2 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA197 + difference 0 2) (sourceB197 + difference 2 0) sourceC197) = raw5519 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5519; decide +kernel
    rw [ha]
    exact (canonical5519 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA197 + difference 0 3) (sourceB197 + difference 3 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA197 + difference 0 3) (sourceB197 + difference 3 0) sourceC197) = raw5520 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5520; decide +kernel
    rw [ha]
    exact (canonical5520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA197 + difference 0 4) (sourceB197 + difference 4 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA197 + difference 0 4) (sourceB197 + difference 4 0) sourceC197) = raw5521 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5521; decide +kernel
    rw [ha]
    exact (canonical5521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA197 + difference 0 5) (sourceB197 + difference 5 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3618) := by
    have ha : (tripleCharges (sourceA197 + difference 0 5) (sourceB197 + difference 5 0) sourceC197) = raw5522 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5522; decide +kernel
    rw [ha]
    exact (canonical5522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA197 + sourceB197) sourceC197) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA197 + sourceB197) sourceC197) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA197 sourceB197 sourceC197 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA197 sourceB197 sourceC197
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm197, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm198 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA198 + difference 0 0) (sourceB198 + difference 0 0) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA198 + difference 0 0) (sourceB198 + difference 0 0) sourceC198) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA198 + difference 1 0) (sourceB198 + difference 0 1) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA198 + difference 1 0) (sourceB198 + difference 0 1) sourceC198) = raw5524 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5524; decide +kernel
    rw [ha]
    exact (canonical5524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA198 + difference 2 0) (sourceB198 + difference 0 2) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA198 + difference 2 0) (sourceB198 + difference 0 2) sourceC198) = raw5525 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5525; decide +kernel
    rw [ha]
    exact (canonical5525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA198 + difference 3 0) (sourceB198 + difference 0 3) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA198 + difference 3 0) (sourceB198 + difference 0 3) sourceC198) = raw5526 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5526; decide +kernel
    rw [ha]
    exact (canonical5526 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA198 + difference 4 0) (sourceB198 + difference 0 4) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1015) := by
    have ha : (tripleCharges (sourceA198 + difference 4 0) (sourceB198 + difference 0 4) sourceC198) = raw5527 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5527; decide +kernel
    rw [ha]
    exact (canonical5527 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA198 + difference 5 0) (sourceB198 + difference 0 5) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1014) := by
    have ha : (tripleCharges (sourceA198 + difference 5 0) (sourceB198 + difference 0 5) sourceC198) = raw5528 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5528; decide +kernel
    rw [ha]
    exact (canonical5528 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA198 + sourceB198) sourceC198) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA198 + sourceB198) sourceC198) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA198 sourceB198 sourceC198 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA198 sourceB198 sourceC198
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm198, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm199 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA199 + difference 1 0) (sourceB199 + difference 0 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA199 + difference 1 0) (sourceB199 + difference 0 1) sourceC199) = raw5524 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5524; decide +kernel
    rw [ha]
    exact (canonical5524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA199 + difference 1 1) (sourceB199 + difference 1 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA199 + difference 1 1) (sourceB199 + difference 1 1) sourceC199) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA199 + difference 1 2) (sourceB199 + difference 2 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA199 + difference 1 2) (sourceB199 + difference 2 1) sourceC199) = raw5529 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5529; decide +kernel
    rw [ha]
    exact (canonical5529 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA199 + difference 1 3) (sourceB199 + difference 3 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA199 + difference 1 3) (sourceB199 + difference 3 1) sourceC199) = raw5530 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5530; decide +kernel
    rw [ha]
    exact (canonical5530 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA199 + difference 1 4) (sourceB199 + difference 4 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA199 + difference 1 4) (sourceB199 + difference 4 1) sourceC199) = raw5531 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5531; decide +kernel
    rw [ha]
    exact (canonical5531 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA199 + difference 1 5) (sourceB199 + difference 5 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA199 + difference 1 5) (sourceB199 + difference 5 1) sourceC199) = raw5532 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5532; decide +kernel
    rw [ha]
    exact (canonical5532 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA199 + sourceB199) sourceC199) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA199 + sourceB199) sourceC199) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA199 sourceB199 sourceC199 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA199 sourceB199 sourceC199
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm199, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm200 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA200 + difference 0 1) (sourceB200 + difference 1 0) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA200 + difference 0 1) (sourceB200 + difference 1 0) sourceC200) = raw5518 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5518; decide +kernel
    rw [ha]
    exact (canonical5518 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA200 + difference 1 1) (sourceB200 + difference 1 1) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA200 + difference 1 1) (sourceB200 + difference 1 1) sourceC200) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA200 + difference 2 1) (sourceB200 + difference 1 2) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA200 + difference 2 1) (sourceB200 + difference 1 2) sourceC200) = raw5533 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5533; decide +kernel
    rw [ha]
    exact (canonical5533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA200 + difference 3 1) (sourceB200 + difference 1 3) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA200 + difference 3 1) (sourceB200 + difference 1 3) sourceC200) = raw5534 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5534; decide +kernel
    rw [ha]
    exact (canonical5534 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA200 + difference 4 1) (sourceB200 + difference 1 4) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA200 + difference 4 1) (sourceB200 + difference 1 4) sourceC200) = raw5535 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5535; decide +kernel
    rw [ha]
    exact (canonical5535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA200 + difference 5 1) (sourceB200 + difference 1 5) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA200 + difference 5 1) (sourceB200 + difference 1 5) sourceC200) = raw5536 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5536; decide +kernel
    rw [ha]
    exact (canonical5536 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA200 + sourceB200) sourceC200) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA200 + sourceB200) sourceC200) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA200 sourceB200 sourceC200 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA200 sourceB200 sourceC200
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm200, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm201 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA201 + difference 4 0) (sourceB201 + difference 0 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1015) := by
    have ha : (tripleCharges (sourceA201 + difference 4 0) (sourceB201 + difference 0 4) sourceC201) = raw5527 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5527; decide +kernel
    rw [ha]
    exact (canonical5527 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA201 + difference 4 1) (sourceB201 + difference 1 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA201 + difference 4 1) (sourceB201 + difference 1 4) sourceC201) = raw5535 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5535; decide +kernel
    rw [ha]
    exact (canonical5535 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA201 + difference 4 2) (sourceB201 + difference 2 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA201 + difference 4 2) (sourceB201 + difference 2 4) sourceC201) = raw5537 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5537; decide +kernel
    rw [ha]
    exact (canonical5537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA201 + difference 4 3) (sourceB201 + difference 3 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA201 + difference 4 3) (sourceB201 + difference 3 4) sourceC201) = raw5538 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5538; decide +kernel
    rw [ha]
    exact (canonical5538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA201 + difference 4 4) (sourceB201 + difference 4 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA201 + difference 4 4) (sourceB201 + difference 4 4) sourceC201) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA201 + difference 4 5) (sourceB201 + difference 5 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA201 + difference 4 5) (sourceB201 + difference 5 4) sourceC201) = raw5539 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5539; decide +kernel
    rw [ha]
    exact (canonical5539 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA201 + sourceB201) sourceC201) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA201 + sourceB201) sourceC201) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA201 sourceB201 sourceC201 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA201 sourceB201 sourceC201
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm201, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck160 : Integer.Sparse.reindex keyMap MixedData.row160 = numericRow160 := by decide +kernel

theorem numericCheck160 (x : Master → ℝ) : Integer.Sparse.eval numericRow160 x =
    (1 : ℝ) * reducedSource160 x := by
  norm_num [numericRow160, reducedSource160, Integer.Sparse.eval, Sparse.eval, nodeValue1042, nodeValue2021, nodeValue2108, nodeValue2253, nodeValue2262, nodeValue2266, nodeValue4084]

theorem reindexCheck161 : Integer.Sparse.reindex keyMap MixedData.row161 = numericRow161 := by decide +kernel

theorem numericCheck161 (x : Master → ℝ) : Integer.Sparse.eval numericRow161 x =
    (1 : ℝ) * reducedSource161 x := by
  norm_num [numericRow161, reducedSource161, Integer.Sparse.eval, Sparse.eval, nodeValue2124, nodeValue2125, nodeValue2126, nodeValue2133, nodeValue2253, nodeValue2513, nodeValue4084]

theorem reindexCheck162 : Integer.Sparse.reindex keyMap MixedData.row162 = numericRow162 := by decide +kernel

theorem numericCheck162 (x : Master → ℝ) : Integer.Sparse.eval numericRow162 x =
    (1 : ℝ) * reducedSource162 x := by
  norm_num [numericRow162, reducedSource162, Integer.Sparse.eval, Sparse.eval, nodeValue1030, nodeValue2014, nodeValue2097, nodeValue2126, nodeValue2253, nodeValue4084]

theorem reindexCheck164 : Integer.Sparse.reindex keyMap MixedData.row164 = numericRow164 := by decide +kernel

theorem numericCheck164 (x : Master → ℝ) : Integer.Sparse.eval numericRow164 x =
    (1 : ℝ) * reducedSource164 x := by
  norm_num [numericRow164, reducedSource164, Integer.Sparse.eval, Sparse.eval, nodeValue3222, nodeValue3803, nodeValue3809, nodeValue3814, nodeValue4092]

theorem reindexCheck165 : Integer.Sparse.reindex keyMap MixedData.row165 = numericRow165 := by decide +kernel

theorem numericCheck165 (x : Master → ℝ) : Integer.Sparse.eval numericRow165 x =
    (1 : ℝ) * reducedSource165 x := by
  norm_num [numericRow165, reducedSource165, Integer.Sparse.eval, Sparse.eval, nodeValue1463, nodeValue1465, nodeValue1466, nodeValue3222, nodeValue4092]

theorem reindexCheck166 : Integer.Sparse.reindex keyMap MixedData.row166 = numericRow166 := by decide +kernel

theorem numericCheck166 (x : Master → ℝ) : Integer.Sparse.eval numericRow166 x =
    (1 : ℝ) * reducedSource166 x := by
  norm_num [numericRow166, reducedSource166, Integer.Sparse.eval, Sparse.eval, nodeValue1463, nodeValue3170, nodeValue3196, nodeValue3222, nodeValue4092]

theorem reindexCheck167 : Integer.Sparse.reindex keyMap MixedData.row167 = numericRow167 := by decide +kernel

theorem numericCheck167 (x : Master → ℝ) : Integer.Sparse.eval numericRow167 x =
    (1 : ℝ) * reducedSource167 x := by
  norm_num [numericRow167, reducedSource167, Integer.Sparse.eval, Sparse.eval, nodeValue2474, nodeValue3217, nodeValue3222, nodeValue3803, nodeValue4092]

theorem reindexCheck168 : Integer.Sparse.reindex keyMap MixedData.row168 = numericRow168 := by decide +kernel

theorem numericCheck168 (x : Master → ℝ) : Integer.Sparse.eval numericRow168 x =
    (1 : ℝ) * reducedSource168 x := by
  norm_num [numericRow168, reducedSource168, Integer.Sparse.eval, Sparse.eval, nodeValue1466, nodeValue3174, nodeValue3180, nodeValue3198, nodeValue3217, nodeValue3222, nodeValue4092]

theorem reindexCheck169 : Integer.Sparse.reindex keyMap MixedData.row169 = numericRow169 := by decide +kernel

theorem numericCheck169 (x : Master → ℝ) : Integer.Sparse.eval numericRow169 x =
    (1 : ℝ) * reducedSource169 x := by
  norm_num [numericRow169, reducedSource169, Integer.Sparse.eval, Sparse.eval, nodeValue2497, nodeValue2716, nodeValue3196, nodeValue3198, nodeValue3222, nodeValue3814, nodeValue4092]

theorem reindexCheck170 : Integer.Sparse.reindex keyMap MixedData.row170 = numericRow170 := by decide +kernel

theorem numericCheck170 (x : Master → ℝ) : Integer.Sparse.eval numericRow170 x =
    (1 : ℝ) * reducedSource170 x := by
  norm_num [numericRow170, reducedSource170, Integer.Sparse.eval, Sparse.eval, nodeValue1465, nodeValue2474, nodeValue2486, nodeValue2497, nodeValue2716, nodeValue3222, nodeValue4092]

theorem reindexCheck171 : Integer.Sparse.reindex keyMap MixedData.row171 = numericRow171 := by decide +kernel

theorem numericCheck171 (x : Master → ℝ) : Integer.Sparse.eval numericRow171 x =
    (1 : ℝ) * reducedSource171 x := by
  norm_num [numericRow171, reducedSource171, Integer.Sparse.eval, Sparse.eval, nodeValue2233, nodeValue3567, nodeValue3618, nodeValue3619, nodeValue4083]

theorem reindexCheck172 : Integer.Sparse.reindex keyMap MixedData.row172 = numericRow172 := by decide +kernel

theorem numericCheck172 (x : Master → ℝ) : Integer.Sparse.eval numericRow172 x =
    (1 : ℝ) * reducedSource172 x := by
  norm_num [numericRow172, reducedSource172, Integer.Sparse.eval, Sparse.eval, nodeValue1014, nodeValue1015, nodeValue1021, nodeValue2233, nodeValue4083]

theorem reindexCheck173 : Integer.Sparse.reindex keyMap MixedData.row173 = numericRow173 := by decide +kernel

theorem numericCheck173 (x : Master → ℝ) : Integer.Sparse.eval numericRow173 x =
    (1 : ℝ) * reducedSource173 x := by
  norm_num [numericRow173, reducedSource173, Integer.Sparse.eval, Sparse.eval, nodeValue1021, nodeValue2089, nodeValue2233, nodeValue2243, nodeValue2245, nodeValue4083]

theorem reindexCheck174 : Integer.Sparse.reindex keyMap MixedData.row174 = numericRow174 := by decide +kernel

theorem numericCheck174 (x : Master → ℝ) : Integer.Sparse.eval numericRow174 x =
    (1 : ℝ) * reducedSource174 x := by
  norm_num [numericRow174, reducedSource174, Integer.Sparse.eval, Sparse.eval, nodeValue2083, nodeValue2084, nodeValue2089, nodeValue2233, nodeValue3567, nodeValue4083]

theorem reindexCheck175 : Integer.Sparse.reindex keyMap MixedData.row175 = numericRow175 := by decide +kernel

theorem numericCheck175 (x : Master → ℝ) : Integer.Sparse.eval numericRow175 x =
    (1 : ℝ) * reducedSource175 x := by
  norm_num [numericRow175, reducedSource175, Integer.Sparse.eval, Sparse.eval, nodeValue1015, nodeValue2084, nodeValue2233, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck352 : Integer.Sparse.reindex keyMap MixedData.row352 = numericRow352 := by decide +kernel

theorem numericCheck352 (x : Master → ℝ) : Integer.Sparse.eval numericRow352 x =
    (1 : ℝ) * reducedSource352 x := by
  norm_num [numericRow352, reducedSource352, Integer.Sparse.eval, Sparse.eval, nodeValue1310, nodeValue2603, nodeValue2783, nodeValue2789, nodeValue4084]

theorem reindexCheck360 : Integer.Sparse.reindex keyMap MixedData.row360 = numericRow360 := by decide +kernel

theorem numericCheck360 (x : Master → ℝ) : Integer.Sparse.eval numericRow360 x =
    (1 : ℝ) * reducedSource360 x := by
  norm_num [numericRow360, reducedSource360, Integer.Sparse.eval, Sparse.eval, nodeValue3544, nodeValue3547, nodeValue3548, nodeValue3627, nodeValue3635, nodeValue4084]

theorem reindexCheck361 : Integer.Sparse.reindex keyMap MixedData.row361 = numericRow361 := by decide +kernel

theorem numericCheck361 (x : Master → ℝ) : Integer.Sparse.eval numericRow361 x =
    (1 : ℝ) * reducedSource361 x := by
  norm_num [numericRow361, reducedSource361, Integer.Sparse.eval, Sparse.eval, nodeValue2262, nodeValue2264, nodeValue2266, nodeValue2291, nodeValue3627, nodeValue4084]

theorem reindexCheck362 : Integer.Sparse.reindex keyMap MixedData.row362 = numericRow362 := by decide +kernel

theorem numericCheck362 (x : Master → ℝ) : Integer.Sparse.eval numericRow362 x =
    (1 : ℝ) * reducedSource362 x := by
  norm_num [numericRow362, reducedSource362, Integer.Sparse.eval, Sparse.eval, nodeValue3627, nodeValue3629, nodeValue3635, nodeValue4084]

theorem reindexCheck363 : Integer.Sparse.reindex keyMap MixedData.row363 = numericRow363 := by decide +kernel

theorem numericCheck363 (x : Master → ℝ) : Integer.Sparse.eval numericRow363 x =
    (1 : ℝ) * reducedSource363 x := by
  norm_num [numericRow363, reducedSource363, Integer.Sparse.eval, Sparse.eval, nodeValue3548, nodeValue3580, nodeValue3582, nodeValue3584, nodeValue3627, nodeValue4084]

theorem reindexCheck364 : Integer.Sparse.reindex keyMap MixedData.row364 = numericRow364 := by decide +kernel

theorem numericCheck364 (x : Master → ℝ) : Integer.Sparse.eval numericRow364 x =
    (1 : ℝ) * reducedSource364 x := by
  norm_num [numericRow364, reducedSource364, Integer.Sparse.eval, Sparse.eval, nodeValue2264, nodeValue3533, nodeValue3582, nodeValue3627, nodeValue3629, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource160 (mixedVector B) = 0 := by
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm182, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1042, h2021, h2108, h2253, h2262, h2266, h4084, reducedSource160] using sourceEq182 B hB

theorem rowSound160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row160 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck160, numericCheck160, reducedZero160 B hB hF, mul_zero]

theorem reducedZero161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource161 (mixedVector B) = 0 := by
  have h2124 : mixedVector B (Sum.inr 2124) = Sparse.eval nodeValue2124 (mixedVector B) := by
    change mixedMoment B node2124 node2124Labels = _
    exact sound2124 B hB hF
  have h2125 : mixedVector B (Sum.inr 2125) = Sparse.eval nodeValue2125 (mixedVector B) := by
    change mixedMoment B node2125 node2125Labels = _
    exact sound2125 B hB hF
  have h2126 : mixedVector B (Sum.inr 2126) = Sparse.eval nodeValue2126 (mixedVector B) := by
    change mixedMoment B node2126 node2126Labels = _
    exact sound2126 B hB hF
  have h2133 : mixedVector B (Sum.inr 2133) = Sparse.eval nodeValue2133 (mixedVector B) := by
    change mixedMoment B node2133 node2133Labels = _
    exact sound2133 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h2513 : mixedVector B (Sum.inr 2513) = Sparse.eval nodeValue2513 (mixedVector B) := by
    change mixedMoment B node2513 node2513Labels = _
    exact sound2513 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm183, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2124, h2125, h2126, h2133, h2253, h2513, h4084, reducedSource161] using sourceEq183 B hB

theorem rowSound161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row161 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck161, numericCheck161, reducedZero161 B hB hF, mul_zero]

theorem reducedZero162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource162 (mixedVector B) = 0 := by
  have h1030 : mixedVector B (Sum.inr 1030) = Sparse.eval nodeValue1030 (mixedVector B) := by
    change mixedMoment B node1030 node1030Labels = _
    exact sound1030 B hB hF
  have h2014 : mixedVector B (Sum.inr 2014) = Sparse.eval nodeValue2014 (mixedVector B) := by
    change mixedMoment B node2014 node2014Labels = _
    exact sound2014 B hB hF
  have h2097 : mixedVector B (Sum.inr 2097) = Sparse.eval nodeValue2097 (mixedVector B) := by
    change mixedMoment B node2097 node2097Labels = _
    exact sound2097 B hB hF
  have h2126 : mixedVector B (Sum.inr 2126) = Sparse.eval nodeValue2126 (mixedVector B) := by
    change mixedMoment B node2126 node2126Labels = _
    exact sound2126 B hB hF
  have h2253 : mixedVector B (Sum.inr 2253) = Sparse.eval nodeValue2253 (mixedVector B) := by
    change mixedMoment B node2253 node2253Labels = _
    exact sound2253 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm184, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1030, h2014, h2097, h2126, h2253, h4084, reducedSource162] using sourceEq184 B hB

theorem rowSound162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row162 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck162, numericCheck162, reducedZero162 B hB hF, mul_zero]

theorem reducedZero164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource164 (mixedVector B) = 0 := by
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm187, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3222, h3803, h3809, h3814, h4092, reducedSource164] using sourceEq187 B hB

theorem rowSound164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row164 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck164, numericCheck164, reducedZero164 B hB hF, mul_zero]

theorem reducedZero165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource165 (mixedVector B) = 0 := by
  have h1463 : mixedVector B (Sum.inr 1463) = Sparse.eval nodeValue1463 (mixedVector B) := by
    change mixedMoment B node1463 node1463Labels = _
    exact sound1463 B hB hF
  have h1465 : mixedVector B (Sum.inr 1465) = Sparse.eval nodeValue1465 (mixedVector B) := by
    change mixedMoment B node1465 node1465Labels = _
    exact sound1465 B hB hF
  have h1466 : mixedVector B (Sum.inr 1466) = Sparse.eval nodeValue1466 (mixedVector B) := by
    change mixedMoment B node1466 node1466Labels = _
    exact sound1466 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm188, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1463, h1465, h1466, h3222, h4092, reducedSource165] using sourceEq188 B hB

theorem rowSound165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row165 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck165, numericCheck165, reducedZero165 B hB hF, mul_zero]

theorem reducedZero166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource166 (mixedVector B) = 0 := by
  have h1463 : mixedVector B (Sum.inr 1463) = Sparse.eval nodeValue1463 (mixedVector B) := by
    change mixedMoment B node1463 node1463Labels = _
    exact sound1463 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm189, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1463, h3170, h3196, h3222, h4092, reducedSource166] using sourceEq189 B hB

theorem rowSound166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row166 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck166, numericCheck166, reducedZero166 B hB hF, mul_zero]

theorem reducedZero167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource167 (mixedVector B) = 0 := by
  have h2474 : mixedVector B (Sum.inr 2474) = Sparse.eval nodeValue2474 (mixedVector B) := by
    change mixedMoment B node2474 node2474Labels = _
    exact sound2474 B hB hF
  have h3217 : mixedVector B (Sum.inr 3217) = Sparse.eval nodeValue3217 (mixedVector B) := by
    change mixedMoment B node3217 node3217Labels = _
    exact sound3217 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3803 : mixedVector B (Sum.inr 3803) = Sparse.eval nodeValue3803 (mixedVector B) := by
    change mixedMoment B node3803 node3803Labels = _
    exact sound3803 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm190, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2474, h3217, h3222, h3803, h4092, reducedSource167] using sourceEq190 B hB

theorem rowSound167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row167 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck167, numericCheck167, reducedZero167 B hB hF, mul_zero]

theorem reducedZero168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource168 (mixedVector B) = 0 := by
  have h1466 : mixedVector B (Sum.inr 1466) = Sparse.eval nodeValue1466 (mixedVector B) := by
    change mixedMoment B node1466 node1466Labels = _
    exact sound1466 B hB hF
  have h3174 : mixedVector B (Sum.inr 3174) = Sparse.eval nodeValue3174 (mixedVector B) := by
    change mixedMoment B node3174 node3174Labels = _
    exact sound3174 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3217 : mixedVector B (Sum.inr 3217) = Sparse.eval nodeValue3217 (mixedVector B) := by
    change mixedMoment B node3217 node3217Labels = _
    exact sound3217 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm191, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1466, h3174, h3180, h3198, h3217, h3222, h4092, reducedSource168] using sourceEq191 B hB

theorem rowSound168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row168 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck168, numericCheck168, reducedZero168 B hB hF, mul_zero]

theorem reducedZero169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource169 (mixedVector B) = 0 := by
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3198 : mixedVector B (Sum.inr 3198) = Sparse.eval nodeValue3198 (mixedVector B) := by
    change mixedMoment B node3198 node3198Labels = _
    exact sound3198 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm192, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2497, h2716, h3196, h3198, h3222, h3814, h4092, reducedSource169] using sourceEq192 B hB

theorem rowSound169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row169 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck169, numericCheck169, reducedZero169 B hB hF, mul_zero]

theorem reducedZero170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource170 (mixedVector B) = 0 := by
  have h1465 : mixedVector B (Sum.inr 1465) = Sparse.eval nodeValue1465 (mixedVector B) := by
    change mixedMoment B node1465 node1465Labels = _
    exact sound1465 B hB hF
  have h2474 : mixedVector B (Sum.inr 2474) = Sparse.eval nodeValue2474 (mixedVector B) := by
    change mixedMoment B node2474 node2474Labels = _
    exact sound2474 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h3222 : mixedVector B (Sum.inr 3222) = Sparse.eval nodeValue3222 (mixedVector B) := by
    change mixedMoment B node3222 node3222Labels = _
    exact sound3222 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm193, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1465, h2474, h2486, h2497, h2716, h3222, h4092, reducedSource170] using sourceEq193 B hB

theorem rowSound170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row170 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck170, numericCheck170, reducedZero170 B hB hF, mul_zero]

theorem reducedZero171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource171 (mixedVector B) = 0 := by
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h3618 : mixedVector B (Sum.inr 3618) = Sparse.eval nodeValue3618 (mixedVector B) := by
    change mixedMoment B node3618 node3618Labels = _
    exact sound3618 B hB hF
  have h3619 : mixedVector B (Sum.inr 3619) = Sparse.eval nodeValue3619 (mixedVector B) := by
    change mixedMoment B node3619 node3619Labels = _
    exact sound3619 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm197, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2233, h3567, h3618, h3619, h4083, reducedSource171] using sourceEq197 B hB

theorem rowSound171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row171 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck171, numericCheck171, reducedZero171 B hB hF, mul_zero]

theorem reducedZero172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource172 (mixedVector B) = 0 := by
  have h1014 : mixedVector B (Sum.inr 1014) = Sparse.eval nodeValue1014 (mixedVector B) := by
    change mixedMoment B node1014 node1014Labels = _
    exact sound1014 B hB hF
  have h1015 : mixedVector B (Sum.inr 1015) = Sparse.eval nodeValue1015 (mixedVector B) := by
    change mixedMoment B node1015 node1015Labels = _
    exact sound1015 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm198, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1014, h1015, h1021, h2233, h4083, reducedSource172] using sourceEq198 B hB

theorem rowSound172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row172 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck172, numericCheck172, reducedZero172 B hB hF, mul_zero]

theorem reducedZero173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource173 (mixedVector B) = 0 := by
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h2243 : mixedVector B (Sum.inr 2243) = Sparse.eval nodeValue2243 (mixedVector B) := by
    change mixedMoment B node2243 node2243Labels = _
    exact sound2243 B hB hF
  have h2245 : mixedVector B (Sum.inr 2245) = Sparse.eval nodeValue2245 (mixedVector B) := by
    change mixedMoment B node2245 node2245Labels = _
    exact sound2245 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm199, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1021, h2089, h2233, h2243, h2245, h4083, reducedSource173] using sourceEq199 B hB

theorem rowSound173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row173 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck173, numericCheck173, reducedZero173 B hB hF, mul_zero]

theorem reducedZero174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource174 (mixedVector B) = 0 := by
  have h2083 : mixedVector B (Sum.inr 2083) = Sparse.eval nodeValue2083 (mixedVector B) := by
    change mixedMoment B node2083 node2083Labels = _
    exact sound2083 B hB hF
  have h2084 : mixedVector B (Sum.inr 2084) = Sparse.eval nodeValue2084 (mixedVector B) := by
    change mixedMoment B node2084 node2084Labels = _
    exact sound2084 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h3567 : mixedVector B (Sum.inr 3567) = Sparse.eval nodeValue3567 (mixedVector B) := by
    change mixedMoment B node3567 node3567Labels = _
    exact sound3567 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm200, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2083, h2084, h2089, h2233, h3567, h4083, reducedSource174] using sourceEq200 B hB

theorem rowSound174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row174 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck174, numericCheck174, reducedZero174 B hB hF, mul_zero]

theorem reducedZero175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource175 (mixedVector B) = 0 := by
  have h1015 : mixedVector B (Sum.inr 1015) = Sparse.eval nodeValue1015 (mixedVector B) := by
    change mixedMoment B node1015 node1015Labels = _
    exact sound1015 B hB hF
  have h2084 : mixedVector B (Sum.inr 2084) = Sparse.eval nodeValue2084 (mixedVector B) := by
    change mixedMoment B node2084 node2084Labels = _
    exact sound2084 B hB hF
  have h2233 : mixedVector B (Sum.inr 2233) = Sparse.eval nodeValue2233 (mixedVector B) := by
    change mixedMoment B node2233 node2233Labels = _
    exact sound2233 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm201, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1015, h2084, h2233, h4083, reducedSource175] using sourceEq201 B hB

theorem rowSound175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row175 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck175, numericCheck175, reducedZero175 B hB hF, mul_zero]

theorem sourceRowsAt160 : MixedData.sourceRows (160 : Fin 2425) =
    MixedData.row160 := by decide +kernel

theorem sourceRowsAt161 : MixedData.sourceRows (161 : Fin 2425) =
    MixedData.row161 := by decide +kernel

theorem sourceRowsAt162 : MixedData.sourceRows (162 : Fin 2425) =
    MixedData.row162 := by decide +kernel

theorem sourceRowsAt163 : MixedData.sourceRows (163 : Fin 2425) =
    MixedData.row163 := by decide +kernel

theorem sourceRowsAt164 : MixedData.sourceRows (164 : Fin 2425) =
    MixedData.row164 := by decide +kernel

theorem sourceRowsAt165 : MixedData.sourceRows (165 : Fin 2425) =
    MixedData.row165 := by decide +kernel

theorem sourceRowsAt166 : MixedData.sourceRows (166 : Fin 2425) =
    MixedData.row166 := by decide +kernel

theorem sourceRowsAt167 : MixedData.sourceRows (167 : Fin 2425) =
    MixedData.row167 := by decide +kernel

theorem sourceRowsAt168 : MixedData.sourceRows (168 : Fin 2425) =
    MixedData.row168 := by decide +kernel

theorem sourceRowsAt169 : MixedData.sourceRows (169 : Fin 2425) =
    MixedData.row169 := by decide +kernel

theorem sourceRowsAt170 : MixedData.sourceRows (170 : Fin 2425) =
    MixedData.row170 := by decide +kernel

theorem sourceRowsAt171 : MixedData.sourceRows (171 : Fin 2425) =
    MixedData.row171 := by decide +kernel

theorem sourceRowsAt172 : MixedData.sourceRows (172 : Fin 2425) =
    MixedData.row172 := by decide +kernel

theorem sourceRowsAt173 : MixedData.sourceRows (173 : Fin 2425) =
    MixedData.row173 := by decide +kernel

theorem sourceRowsAt174 : MixedData.sourceRows (174 : Fin 2425) =
    MixedData.row174 := by decide +kernel

theorem sourceRowsAt175 : MixedData.sourceRows (175 : Fin 2425) =
    MixedData.row175 := by decide +kernel

theorem chunkSound10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 10) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 160 ∨ k.val = 161 ∨ k.val = 162 ∨ k.val = 163 ∨ k.val = 164 ∨ k.val = 165 ∨ k.val = 166 ∨ k.val = 167 ∨ k.val = 168 ∨ k.val = 169 ∨ k.val = 170 ∨ k.val = 171 ∨ k.val = 172 ∨ k.val = 173 ∨ k.val = 174 ∨ k.val = 175 := by omega
  rcases heq with h160 | h161 | h162 | h163 | h164 | h165 | h166 | h167 | h168 | h169 | h170 | h171 | h172 | h173 | h174 | h175
  · have he : k = (160 : Fin 2425) := Fin.ext h160
    subst k
    rw [sourceRowsAt160]
    exact rowSound160 B hB hF
  · have he : k = (161 : Fin 2425) := Fin.ext h161
    subst k
    rw [sourceRowsAt161]
    exact rowSound161 B hB hF
  · have he : k = (162 : Fin 2425) := Fin.ext h162
    subst k
    rw [sourceRowsAt162]
    exact rowSound162 B hB hF
  · have he : k = (163 : Fin 2425) := Fin.ext h163
    subst k
    rw [sourceRowsAt163]
    exact rowSound163_e B hB hF
  · have he : k = (164 : Fin 2425) := Fin.ext h164
    subst k
    rw [sourceRowsAt164]
    exact rowSound164 B hB hF
  · have he : k = (165 : Fin 2425) := Fin.ext h165
    subst k
    rw [sourceRowsAt165]
    exact rowSound165 B hB hF
  · have he : k = (166 : Fin 2425) := Fin.ext h166
    subst k
    rw [sourceRowsAt166]
    exact rowSound166 B hB hF
  · have he : k = (167 : Fin 2425) := Fin.ext h167
    subst k
    rw [sourceRowsAt167]
    exact rowSound167 B hB hF
  · have he : k = (168 : Fin 2425) := Fin.ext h168
    subst k
    rw [sourceRowsAt168]
    exact rowSound168 B hB hF
  · have he : k = (169 : Fin 2425) := Fin.ext h169
    subst k
    rw [sourceRowsAt169]
    exact rowSound169 B hB hF
  · have he : k = (170 : Fin 2425) := Fin.ext h170
    subst k
    rw [sourceRowsAt170]
    exact rowSound170 B hB hF
  · have he : k = (171 : Fin 2425) := Fin.ext h171
    subst k
    rw [sourceRowsAt171]
    exact rowSound171 B hB hF
  · have he : k = (172 : Fin 2425) := Fin.ext h172
    subst k
    rw [sourceRowsAt172]
    exact rowSound172 B hB hF
  · have he : k = (173 : Fin 2425) := Fin.ext h173
    subst k
    rw [sourceRowsAt173]
    exact rowSound173 B hB hF
  · have he : k = (174 : Fin 2425) := Fin.ext h174
    subst k
    rw [sourceRowsAt174]
    exact rowSound174 B hB hF
  · have he : k = (175 : Fin 2425) := Fin.ext h175
    subst k
    rw [sourceRowsAt175]
    exact rowSound175 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource352 (mixedVector B) = 0 := by
  have h1310 : mixedVector B (Sum.inr 1310) = Sparse.eval nodeValue1310 (mixedVector B) := by
    change mixedMoment B node1310 node1310Labels = _
    exact sound1310 B hB hF
  have h2603 : mixedVector B (Sum.inr 2603) = Sparse.eval nodeValue2603 (mixedVector B) := by
    change mixedMoment B node2603 node2603Labels = _
    exact sound2603 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h2789 : mixedVector B (Sum.inr 2789) = Sparse.eval nodeValue2789 (mixedVector B) := by
    change mixedMoment B node2789 node2789Labels = _
    exact sound2789 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm420, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1310, h2603, h2783, h2789, h4084, reducedSource352] using sourceEq420 B hB

theorem rowSound352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row352 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck352, numericCheck352, reducedZero352 B hB hF, mul_zero]

theorem reducedZero360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource360 (mixedVector B) = 0 := by
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3547 : mixedVector B (Sum.inr 3547) = Sparse.eval nodeValue3547 (mixedVector B) := by
    change mixedMoment B node3547 node3547Labels = _
    exact sound3547 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h3635 : mixedVector B (Sum.inr 3635) = Sparse.eval nodeValue3635 (mixedVector B) := by
    change mixedMoment B node3635 node3635Labels = _
    exact sound3635 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm428, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3544, h3547, h3548, h3627, h3635, h4084, reducedSource360] using sourceEq428 B hB

theorem rowSound360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row360 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck360, numericCheck360, reducedZero360 B hB hF, mul_zero]

theorem reducedZero361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource361 (mixedVector B) = 0 := by
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h2291 : mixedVector B (Sum.inr 2291) = Sparse.eval nodeValue2291 (mixedVector B) := by
    change mixedMoment B node2291 node2291Labels = _
    exact sound2291 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm429, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2262, h2264, h2266, h2291, h3627, h4084, reducedSource361] using sourceEq429 B hB

theorem rowSound361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row361 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck361, numericCheck361, reducedZero361 B hB hF, mul_zero]

theorem reducedZero362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource362 (mixedVector B) = 0 := by
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h3629 : mixedVector B (Sum.inr 3629) = Sparse.eval nodeValue3629 (mixedVector B) := by
    change mixedMoment B node3629 node3629Labels = _
    exact sound3629 B hB hF
  have h3635 : mixedVector B (Sum.inr 3635) = Sparse.eval nodeValue3635 (mixedVector B) := by
    change mixedMoment B node3635 node3635Labels = _
    exact sound3635 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm430, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3627, h3629, h3635, h4084, reducedSource362] using sourceEq430 B hB

theorem rowSound362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row362 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck362, numericCheck362, reducedZero362 B hB hF, mul_zero]

theorem reducedZero363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource363 (mixedVector B) = 0 := by
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm431, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3548, h3580, h3582, h3584, h3627, h4084, reducedSource363] using sourceEq431 B hB

theorem rowSound363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row363 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck363, numericCheck363, reducedZero363 B hB hF, mul_zero]

theorem reducedZero364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource364 (mixedVector B) = 0 := by
  have h2264 : mixedVector B (Sum.inr 2264) = Sparse.eval nodeValue2264 (mixedVector B) := by
    change mixedMoment B node2264 node2264Labels = _
    exact sound2264 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h3629 : mixedVector B (Sum.inr 3629) = Sparse.eval nodeValue3629 (mixedVector B) := by
    change mixedMoment B node3629 node3629Labels = _
    exact sound3629 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm432, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2264, h3533, h3582, h3627, h3629, h4084, reducedSource364] using sourceEq432 B hB

theorem rowSound364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row364 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck364, numericCheck364, reducedZero364 B hB hF, mul_zero]

theorem sourceRowsAt352 : MixedData.sourceRows (352 : Fin 2425) =
    MixedData.row352 := by decide +kernel

theorem sourceRowsAt353 : MixedData.sourceRows (353 : Fin 2425) =
    MixedData.row353 := by decide +kernel

theorem sourceRowsAt354 : MixedData.sourceRows (354 : Fin 2425) =
    MixedData.row354 := by decide +kernel

theorem sourceRowsAt355 : MixedData.sourceRows (355 : Fin 2425) =
    MixedData.row355 := by decide +kernel

theorem sourceRowsAt356 : MixedData.sourceRows (356 : Fin 2425) =
    MixedData.row356 := by decide +kernel

theorem sourceRowsAt357 : MixedData.sourceRows (357 : Fin 2425) =
    MixedData.row357 := by decide +kernel

theorem sourceRowsAt358 : MixedData.sourceRows (358 : Fin 2425) =
    MixedData.row358 := by decide +kernel

theorem sourceRowsAt359 : MixedData.sourceRows (359 : Fin 2425) =
    MixedData.row359 := by decide +kernel

theorem sourceRowsAt360 : MixedData.sourceRows (360 : Fin 2425) =
    MixedData.row360 := by decide +kernel

theorem sourceRowsAt361 : MixedData.sourceRows (361 : Fin 2425) =
    MixedData.row361 := by decide +kernel

theorem sourceRowsAt362 : MixedData.sourceRows (362 : Fin 2425) =
    MixedData.row362 := by decide +kernel

theorem sourceRowsAt363 : MixedData.sourceRows (363 : Fin 2425) =
    MixedData.row363 := by decide +kernel

theorem sourceRowsAt364 : MixedData.sourceRows (364 : Fin 2425) =
    MixedData.row364 := by decide +kernel

theorem sourceRowsAt365 : MixedData.sourceRows (365 : Fin 2425) =
    MixedData.row365 := by decide +kernel

theorem sourceRowsAt366 : MixedData.sourceRows (366 : Fin 2425) =
    MixedData.row366 := by decide +kernel

theorem sourceRowsAt367 : MixedData.sourceRows (367 : Fin 2425) =
    MixedData.row367 := by decide +kernel

theorem chunkSound22 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 22) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 352 ∨ k.val = 353 ∨ k.val = 354 ∨ k.val = 355 ∨ k.val = 356 ∨ k.val = 357 ∨ k.val = 358 ∨ k.val = 359 ∨ k.val = 360 ∨ k.val = 361 ∨ k.val = 362 ∨ k.val = 363 ∨ k.val = 364 ∨ k.val = 365 ∨ k.val = 366 ∨ k.val = 367 := by omega
  rcases heq with h352 | h353 | h354 | h355 | h356 | h357 | h358 | h359 | h360 | h361 | h362 | h363 | h364 | h365 | h366 | h367
  · have he : k = (352 : Fin 2425) := Fin.ext h352
    subst k
    rw [sourceRowsAt352]
    exact rowSound352 B hB hF
  · have he : k = (353 : Fin 2425) := Fin.ext h353
    subst k
    rw [sourceRowsAt353]
    exact rowSound353_e B hB hF
  · have he : k = (354 : Fin 2425) := Fin.ext h354
    subst k
    rw [sourceRowsAt354]
    exact rowSound354_e B hB hF
  · have he : k = (355 : Fin 2425) := Fin.ext h355
    subst k
    rw [sourceRowsAt355]
    exact rowSound355_e B hB hF
  · have he : k = (356 : Fin 2425) := Fin.ext h356
    subst k
    rw [sourceRowsAt356]
    exact rowSound356_e B hB hF
  · have he : k = (357 : Fin 2425) := Fin.ext h357
    subst k
    rw [sourceRowsAt357]
    exact rowSound357_e B hB hF
  · have he : k = (358 : Fin 2425) := Fin.ext h358
    subst k
    rw [sourceRowsAt358]
    exact rowSound358_e B hB hF
  · have he : k = (359 : Fin 2425) := Fin.ext h359
    subst k
    rw [sourceRowsAt359]
    exact rowSound359_e B hB hF
  · have he : k = (360 : Fin 2425) := Fin.ext h360
    subst k
    rw [sourceRowsAt360]
    exact rowSound360 B hB hF
  · have he : k = (361 : Fin 2425) := Fin.ext h361
    subst k
    rw [sourceRowsAt361]
    exact rowSound361 B hB hF
  · have he : k = (362 : Fin 2425) := Fin.ext h362
    subst k
    rw [sourceRowsAt362]
    exact rowSound362 B hB hF
  · have he : k = (363 : Fin 2425) := Fin.ext h363
    subst k
    rw [sourceRowsAt363]
    exact rowSound363 B hB hF
  · have he : k = (364 : Fin 2425) := Fin.ext h364
    subst k
    rw [sourceRowsAt364]
    exact rowSound364 B hB hF
  · have he : k = (365 : Fin 2425) := Fin.ext h365
    subst k
    rw [sourceRowsAt365]
    exact rowSound365_e B hB hF
  · have he : k = (366 : Fin 2425) := Fin.ext h366
    subst k
    rw [sourceRowsAt366]
    exact rowSound366_e B hB hF
  · have he : k = (367 : Fin 2425) := Fin.ext h367
    subst k
    rw [sourceRowsAt367]
    exact rowSound367_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem allChunksSound (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (c : Fin 152) (k : Fin 2425)
    (hk : k.val / 16 = c.val) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  fin_cases c
  · exact chunkSound0_e B hB hF k hk
  · exact chunkSound1_e B hB hF k hk
  · exact chunkSound2_e B hB hF k hk
  · exact chunkSound3_e B hB hF k hk
  · exact chunkSound4_e B hB hF k hk
  · exact chunkSound5_e B hB hF k hk
  · exact chunkSound6_e B hB hF k hk
  · exact chunkSound7_e B hB hF k hk
  · exact chunkSound8_e B hB hF k hk
  · exact chunkSound9_e B hB hF k hk
  · exact chunkSound10 B hB hF k hk
  · exact chunkSound11_e B hB hF k hk
  · exact chunkSound12_e B hB hF k hk
  · exact chunkSound13_e B hB hF k hk
  · exact chunkSound14_e B hB hF k hk
  · exact chunkSound15_e B hB hF k hk
  · exact chunkSound16_e B hB hF k hk
  · exact chunkSound17_e B hB hF k hk
  · exact chunkSound18_e B hB hF k hk
  · exact chunkSound19_e B hB hF k hk
  · exact chunkSound20_e B hB hF k hk
  · exact chunkSound21_e B hB hF k hk
  · exact chunkSound22 B hB hF k hk
  · exact chunkSound23_e B hB hF k hk
  · exact chunkSound24_e B hB hF k hk
  · exact chunkSound25_e B hB hF k hk
  · exact chunkSound26_e B hB hF k hk
  · exact chunkSound27_e B hB hF k hk
  · exact chunkSound28_e B hB hF k hk
  · exact chunkSound29_e B hB hF k hk
  · exact chunkSound30_e B hB hF k hk
  · exact chunkSound31_e B hB hF k hk
  · exact chunkSound32_e B hB hF k hk
  · exact chunkSound33_e B hB hF k hk
  · exact chunkSound34_e B hB hF k hk
  · exact chunkSound35_e B hB hF k hk
  · exact chunkSound36_e B hB hF k hk
  · exact chunkSound37_e B hB hF k hk
  · exact chunkSound38_e B hB hF k hk
  · exact chunkSound39_e B hB hF k hk
  · exact chunkSound40_e B hB hF k hk
  · exact chunkSound41_e B hB hF k hk
  · exact chunkSound42_e B hB hF k hk
  · exact chunkSound43_e B hB hF k hk
  · exact chunkSound44_e B hB hF k hk
  · exact chunkSound45_e B hB hF k hk
  · exact chunkSound46_e B hB hF k hk
  · exact chunkSound47_e B hB hF k hk
  · exact chunkSound48_e B hB hF k hk
  · exact chunkSound49_e B hB hF k hk
  · exact chunkSound50_e B hB hF k hk
  · exact chunkSound51_e B hB hF k hk
  · exact chunkSound52_e B hB hF k hk
  · exact chunkSound53_e B hB hF k hk
  · exact chunkSound54_e B hB hF k hk
  · exact chunkSound55_e B hB hF k hk
  · exact chunkSound56_e B hB hF k hk
  · exact chunkSound57_e B hB hF k hk
  · exact chunkSound58_e B hB hF k hk
  · exact chunkSound59_e B hB hF k hk
  · exact chunkSound60_e B hB hF k hk
  · exact chunkSound61_e B hB hF k hk
  · exact chunkSound62_e B hB hF k hk
  · exact chunkSound63_e B hB hF k hk
  · exact chunkSound64_e B hB hF k hk
  · exact chunkSound65_e B hB hF k hk
  · exact chunkSound66_e B hB hF k hk
  · exact chunkSound67_e B hB hF k hk
  · exact chunkSound68_e B hB hF k hk
  · exact chunkSound69_e B hB hF k hk
  · exact chunkSound70_e B hB hF k hk
  · exact chunkSound71_e B hB hF k hk
  · exact chunkSound72_e B hB hF k hk
  · exact chunkSound73_e B hB hF k hk
  · exact chunkSound74_e B hB hF k hk
  · exact chunkSound75_e B hB hF k hk
  · exact chunkSound76_e B hB hF k hk
  · exact chunkSound77_e B hB hF k hk
  · exact chunkSound78_e B hB hF k hk
  · exact chunkSound79_e B hB hF k hk
  · exact chunkSound80_e B hB hF k hk
  · exact chunkSound81_e B hB hF k hk
  · exact chunkSound82_e B hB hF k hk
  · exact chunkSound83_e B hB hF k hk
  · exact chunkSound84_e B hB hF k hk
  · exact chunkSound85_e B hB hF k hk
  · exact chunkSound86_e B hB hF k hk
  · exact chunkSound87_e B hB hF k hk
  · exact chunkSound88_e B hB hF k hk
  · exact chunkSound89_e B hB hF k hk
  · exact chunkSound90_e B hB hF k hk
  · exact chunkSound91_e B hB hF k hk
  · exact chunkSound92_e B hB hF k hk
  · exact chunkSound93_e B hB hF k hk
  · exact chunkSound94_e B hB hF k hk
  · exact chunkSound95_e B hB hF k hk
  · exact chunkSound96_e B hB hF k hk
  · exact chunkSound97_e B hB hF k hk
  · exact chunkSound98_e B hB hF k hk
  · exact chunkSound99_e B hB hF k hk
  · exact chunkSound100_e B hB hF k hk
  · exact chunkSound101_e B hB hF k hk
  · exact chunkSound102_e B hB hF k hk
  · exact chunkSound103_e B hB hF k hk
  · exact chunkSound104_e B hB hF k hk
  · exact chunkSound105_e B hB hF k hk
  · exact chunkSound106_e B hB hF k hk
  · exact chunkSound107_e B hB hF k hk
  · exact chunkSound108_e B hB hF k hk
  · exact chunkSound109_e B hB hF k hk
  · exact chunkSound110_e B hB hF k hk
  · exact chunkSound111_e B hB hF k hk
  · exact chunkSound112_e B hB hF k hk
  · exact chunkSound113_e B hB hF k hk
  · exact chunkSound114_e B hB hF k hk
  · exact chunkSound115_e B hB hF k hk
  · exact chunkSound116_e B hB hF k hk
  · exact chunkSound117_e B hB hF k hk
  · exact chunkSound118_e B hB hF k hk
  · exact chunkSound119_e B hB hF k hk
  · exact chunkSound120_e B hB hF k hk
  · exact chunkSound121_e B hB hF k hk
  · exact chunkSound122_e B hB hF k hk
  · exact chunkSound123_e B hB hF k hk
  · exact chunkSound124_e B hB hF k hk
  · exact chunkSound125_e B hB hF k hk
  · exact chunkSound126_e B hB hF k hk
  · exact chunkSound127_e B hB hF k hk
  · exact chunkSound128_e B hB hF k hk
  · exact chunkSound129_e B hB hF k hk
  · exact chunkSound130_e B hB hF k hk
  · exact chunkSound131_e B hB hF k hk
  · exact chunkSound132_e B hB hF k hk
  · exact chunkSound133_e B hB hF k hk
  · exact chunkSound134_e B hB hF k hk
  · exact chunkSound135_e B hB hF k hk
  · exact chunkSound136_e B hB hF k hk
  · exact chunkSound137_e B hB hF k hk
  · exact chunkSound138_e B hB hF k hk
  · exact chunkSound139_e B hB hF k hk
  · exact chunkSound140_e B hB hF k hk
  · exact chunkSound141_e B hB hF k hk
  · exact chunkSound142_e B hB hF k hk
  · exact chunkSound143_e B hB hF k hk
  · exact chunkSound144_e B hB hF k hk
  · exact chunkSound145_e B hB hF k hk
  · exact chunkSound146_e B hB hF k hk
  · exact chunkSound147_e B hB hF k hk
  · exact chunkSound148_e B hB hF k hk
  · exact chunkSound149_e B hB hF k hk
  · exact chunkSound150_e B hB hF k hk
  · exact chunkSound151_e B hB hF k hk

theorem allRowsSound_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  exact allChunksSound B hB hF ⟨k.val / 16, by omega⟩ k rfl

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.allRowsSound_e_oai
