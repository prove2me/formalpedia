-- Prove2me | solution 1 for GlobalTheory.WpFam.DerivExpansion.row_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:07.814421+00:00
-- url     : https://prove2.me/submissions/74199178-7261-4c31-9e0c-fa20c8497285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassPStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsion
import Theorems.Thm_GlobalTheory_WpFam_DerivExpansion_tsum_inv_cube
import Theorems.Thm_GlobalTheory_T_rowSums_two_three_closedForm_real_nonInteger


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.DerivExpansion
namespace GlobalTheory.WpFam.DerivExpansion
theorem _root_.solution (N : ℕ) [NeZero N] (j : ZMod N) :
    ∑' m : ℤ, 1 / (((j.val : ℂ)) / N + m) ^ 3 =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (ch N j * (1 + ch N j) / (1 - ch N j) ^ 3) := by
  rcases eq_or_ne j 0 with rfl | hj
  · have hc : ch N 0 = 1 := by simp [ch]
    simp only [ZMod.val_zero, Nat.cast_zero, zero_div, zero_add, hc, sub_self]
    rw [tsum_inv_cube]
    simp
  · set w : ℂ := ((j.val : ℂ)) / N with hw
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have him : w.im = 0 := by simp [hw, -ZMod.natCast_val]
    have hnot : ∀ n : ℤ, w ≠ n := by
      intro n hn
      rw [hw, div_eq_iff hN] at hn
      have hz : (j.val : ℤ) = n * N := by exact_mod_cast hn
      have h1 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj ((ZMod.val_eq_zero j).mp h))
      have h2 : j.val < N := ZMod.val_lt j
      have h1' : (0 : ℤ) < j.val := by exact_mod_cast h1
      have h2' : (j.val : ℤ) < N := by exact_mod_cast h2
      rcases le_or_gt n 0 with h | h
      · nlinarith
      · nlinarith
    have hc : ch N j = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) := by
      rw [hw]
      unfold ch
      congr 1
      ring
    rw [hc]
    exact (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger w him hnot).2
end GlobalTheory.WpFam.DerivExpansion
