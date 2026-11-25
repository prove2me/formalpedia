-- Prove2me | solution 1 for GlobalTheory.abs_inner_le_of_isRed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:01:54.148027+00:00
-- url     : https://prove2.me/submissions/40b080ad-1af2-4c1b-982b-6f85be1d0b8b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Theorems.Thm_GlobalTheory_rpow_half_sq
import Theorems.Thm_GlobalTheory_nu_sq_mul_le_norm_sq
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_gs_sq_le_pow
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_b_eq_sum
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_inner_gs_comb
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_mu_of_lt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_mu_self
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_eq_zero_of
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_nu_top
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
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℤ) (i : Fin d) :
    |⟪b i, ∑ l, (c l : ℝ) • b l⟫_ℝ| ≤
      (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * ‖∑ l, (c l : ℝ) • b l‖ ^ 2 := by
  classical
  set x := ∑ l, (c l : ℝ) • b l with hx
  set s := (2 : ℝ) ^ ((d : ℝ) / 2) with hs
  have hs0 : 0 < s := by positivity
  by_cases hc : c = 0
  · simp [hx, hc]
  obtain ⟨t, ht, hmax⟩ := exists_max_image (univ.filter fun l => c l ≠ 0) id
    (by simpa [Finset.Nonempty, funext_iff] using hc)
  have ht0 : c t ≠ 0 := (mem_filter.1 ht).2
  have htop : ∀ l, t < l → (c l : ℝ) = 0 := by
    intro l hl
    by_contra h
    exact absurd (hmax l (mem_filter.2 ⟨mem_univ _, by exact_mod_cast h⟩)) (not_le.2 hl)
  have hgt : ‖gs b t‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h1 := nu_sq_mul_le_norm_sq b hr.1 (fun l => (c l : ℝ)) t
    rw [nu_top b hr.1 _ t htop] at h1
    have h2 : (1 : ℝ) ≤ (c t : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ c t ^ 2 := by
        have := sq_pos_of_ne_zero ht0
        omega
      exact_mod_cast this
    nlinarith [sq_nonneg ‖gs b t‖]
  have hterm : ∀ j, |⟪mu b i j • gs b j, x⟫_ℝ| ≤ s * ‖x‖ ^ 2 := by
    intro j
    have hmu : |mu b i j| ≤ 1 := by
      rcases lt_trichotomy j i with h | h | h
      · linarith [hr.2.1 i j h]
      · rw [h, mu_self b hr.1, abs_one]
      · rw [mu_of_lt b h, abs_zero]; exact zero_le_one
    rw [real_inner_smul_left, abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hmu).trans ?_
    rcases le_or_gt j t with h | h
    · have h1 := gs_sq_le_pow b hr t j h
      have h2 : (2 : ℝ) ^ (t.val - j.val) ≤ 2 ^ d :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : ‖gs b j‖ ≤ s * ‖x‖ := by
        refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
        rw [mul_pow, hs, rpow_half_sq]
        exact h1.trans (mul_le_mul h2 hgt (sq_nonneg _) (by positivity))
      calc _ ≤ ‖gs b j‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ s * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = _ := by ring
    · rw [hx, inner_gs_comb b hr.1, nu_eq_zero_of b _ j fun l hl => htop l (h.trans_le hl)]
      rw [zero_mul, abs_zero]; positivity
  conv_lhs => rw [b_eq_sum b hr.1 i, sum_inner]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => hterm j).trans_eq ?_)
  simp [mul_assoc]
end GlobalTheory
