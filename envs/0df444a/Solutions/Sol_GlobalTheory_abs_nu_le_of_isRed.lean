-- Prove2me | solution 1 for GlobalTheory.abs_nu_le_of_isRed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:35.045512+00:00
-- url     : https://prove2.me/submissions/2811a7db-e790-4e33-9c3b-274c74b6d7f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Theorems.Thm_GlobalTheory_rpow_half_sq
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_babai
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_sq_comb
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_eq_zero_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_sub
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_sum_gs_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
noncomputable section
open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder
open GlobalTheory
open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (hmin : ∀ w : Fin d → ℤ, ‖∑ l, c l • b l‖ ^ 2 ≤ ‖∑ l, (c l - N * w l) • b l‖ ^ 2)
    (t : Fin d) : |nu b c t| ≤ (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N := by
  obtain ⟨w, hw0, hw⟩ := babai b hr.1 c hN (t.val + 1) t.isLt
  have h := hmin w
  rw [norm_sq_comb b hr.1, norm_sq_comb b hr.1,
    ← sum_filter_add_sum_filter_not univ (fun j : Fin d => j.val ≤ t.val),
    ← sum_filter_add_sum_filter_not univ (fun j : Fin d => j.val ≤ t.val)] at h
  have e : ∑ j ∈ univ.filter (fun j : Fin d => ¬ j.val ≤ t.val),
      nu b (fun l => c l - N * w l) j ^ 2 * ‖gs b j‖ ^ 2 =
      ∑ j ∈ univ.filter (fun j : Fin d => ¬ j.val ≤ t.val), nu b c j ^ 2 * ‖gs b j‖ ^ 2 := by
    refine sum_congr rfl fun j hj => ?_
    have hj' : ¬ j.val ≤ t.val := (mem_filter.1 hj).2
    rw [nu_sub, nu_eq_zero_of b (fun l => (w l : ℝ)) j fun l hl => by
      rw [hw0 l (by rw [Fin.le_def] at hl; omega), Int.cast_zero]]
    simp
  rw [e, add_le_add_iff_right] at h
  have h1 : nu b c t ^ 2 * ‖gs b t‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val), nu b c j ^ 2 * ‖gs b j‖ ^ 2 :=
    single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
      (fun k _ => by positivity) (mem_filter.2 ⟨mem_univ _, le_rfl⟩)
  have h2 : ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val),
      nu b (fun l => c l - N * w l) j ^ 2 * ‖gs b j‖ ^ 2 ≤
      (N / 2) ^ 2 * ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val), ‖gs b j‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw j (Nat.lt_succ_of_le (mem_filter.1 hj).2)) 2
  have h3 := sum_gs_le b hr.2.2 t.val t.isLt
  have h4 : (2 : ℝ) ^ (t.val + 1) - 1 ≤ 2 ^ d := by
    have : (2 : ℝ) ^ (t.val + 1) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) t.isLt
    linarith
  have hg : 0 < ‖gs b t‖ ^ 2 := by have := gs_ne_zero b hr.1 t; positivity
  have h5 : nu b c t ^ 2 * ‖gs b t‖ ^ 2 ≤ ((N / 2) ^ 2 * 2 ^ d) * ‖gs b t‖ ^ 2 := by
    rw [mul_assoc]
    exact (h1.trans h).trans (h2.trans (mul_le_mul_of_nonneg_left
      (h3.trans (mul_le_mul_of_nonneg_right h4 hg.le)) (sq_nonneg _)))
  refine abs_le_of_sq_le_sq ((le_of_mul_le_mul_right h5 hg).trans_eq ?_) (by positivity)
  rw [Real.rpow_sub_one (by norm_num), mul_pow, div_pow, div_pow, rpow_half_sq]
  ring
end GlobalTheory
