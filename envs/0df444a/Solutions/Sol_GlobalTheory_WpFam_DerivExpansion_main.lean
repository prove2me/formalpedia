-- Prove2me | solution 1 for GlobalTheory.WpFam.DerivExpansion.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:39.840319+00:00
-- url     : https://prove2.me/submissions/9d070a02-d4c9-42d5-9745-64eee530d53f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumRowsInvCubeDerivWeierstrassPStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsion
import Theorems.Thm_GlobalTheory_WpFam_DerivExpansion_row_eq
import Theorems.Thm_GlobalTheory_T_hasSum_rows_inv_cube_derivWeierstrassP
import Theorems.Thm_GlobalTheory_T_torsionPoint_rows_sum_eq_divisor_series


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
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  intro N _ x
  unfold HasQ
  intro τ
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 2 τ x _ (by norm_num) (GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP τ (tors N τ x))
  set q := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set c0 : ℂ := if x 0 = 0 then ch N (x 1) * (1 + ch N (x 1)) / (1 - ch N (x 1)) ^ 3 else 0 with hc0
  have h0 : cSum N 2 (-1) x 0 = 0 := by simp [cSum]
  have hT' : HasSum (fun k : ℕ => cSum N 2 (-1) x k * q ^ k) T := by
    have e1 : ((-1 : ℂ)) ^ (2 + 1) = -1 := by norm_num
    simpa only [e1] using hT
  have hsum : HasSum (fun n : ℕ => cD N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N))
      (c0 + T) := by
    have hA : HasSum (fun n : ℕ => if n = 0 then c0 else 0) c0 := hasSum_ite_eq 0 c0
    convert hA.add hT' using 1
    funext n
    have hexp : Complex.exp (2 * Real.pi * Complex.I * n * τ / N) = q ^ n := by
      rw [hq, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [cD, h0, hc0]
    · simp [cD, hn]
  convert hsum using 1
  have hrow : (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (2 + 1) else 0) =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * c0 := by
    rw [hc0]
    split_ifs
    · exact row_eq N (x 1)
    · simp
  have hf : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
  rw [hrow, hf] at hS
  simp only [wpd]
  rw [div_eq_iff (pow_ne_zero 3 hπ)]
  linear_combination (-2) * hS
end GlobalTheory.WpFam.DerivExpansion
