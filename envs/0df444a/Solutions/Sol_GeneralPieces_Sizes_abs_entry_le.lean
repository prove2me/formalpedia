-- Prove2me | solution 1 for GeneralPieces.Sizes.abs_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:30:56.552299+00:00
-- url     : https://prove2.me/submissions/9a90730e-6c57-40c7-8bab-cb4d611f6e89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
import Theorems.Thm_GeneralPieces_Sizes_coef_opMon_cons
import Theorems.Thm_GeneralPieces_Sizes_card_terms_le
import Theorems.Thm_GeneralPieces_Sizes_wt_erase_le
import Theorems.Thm_GeneralPieces_Sizes_abs_mult_l_le
import Theorems.Thm_GeneralPieces_Sizes_abs_mult_k_le
import Theorems.Thm_GeneralPieces_Lex_IsMu_wt
import Theorems.Thm_GeneralPieces_Ring_coef_tpow
import Theorems.Thm_GeneralPieces_Ring_opMon_nil


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
namespace GeneralPieces.Sizes
theorem _root_.solution {h : ℕ} (hh : 1 ≤ h) (a : List ℕ+) (ha : ∀ n ∈ a, (n : ℕ) ≤ h) (r : ℤ) {σ' σ : Ptn} (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) :
    |coef σ' (opMon a r (tpow σ))| ≤ (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ a.length := by
  induction a generalizing r σ' σ with
  | nil =>
    rw [opMon_nil, List.length_nil, pow_zero]
    split_ifs
    · rw [coef_tpow]
      split_ifs <;> simp
    · simp [coef]
  | cons n a ih =>
    have ih' := fun (r : ℤ) (σ' σ : Ptn) (h1 : wt σ' ≤ 4 * h) (h2 : wt σ ≤ 4 * h) => ih (fun m hm => ha m (List.mem_cons_of_mem _ hm)) r h1 h2
    have hn := ha n List.mem_cons_self
    rw [coef_opMon_cons, List.length_cons, pow_succ]
    generalize (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) ^ a.length = B at ih' ⊢
    have hB : 0 ≤ B := (abs_nonneg _).trans (ih' r σ' σ h1 h2)
    have hK : (0 : ℚ) ≤ 4 * h * 2 ^ (5 * h) := by positivity
    have b1 : |∑ l ∈ σ'.toFinset, ((binom (((l : ℕ) : ℤ) - 1) ((n : ℤ) - 1) : ℤ) : ℚ) * coef (σ'.erase l) (opMon a (r - (l : ℕ)) (tpow σ))|
        ≤ #σ'.toFinset • (4 * h * 2 ^ (5 * h) * B) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_card_nsmul _ _ _ fun l hl => ?_)
      rw [abs_mul]
      refine mul_le_mul ?_ (ih' _ _ _ ((wt_erase_le σ' l).trans h1) h2) (abs_nonneg _) hK
      exact_mod_cast abs_mult_l_le hh hn h1 (Multiset.mem_toFinset.1 hl)
    have b2 : |∑ k ∈ σ.toFinset, ((binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k) : ℤ) : ℚ) *
          coef σ' (opMon a (r + (k : ℕ)) (tpow (σ.erase k)))| ≤ #σ.toFinset • (4 * h * 2 ^ (5 * h) * B) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_card_nsmul _ _ _ fun k hk => ?_)
      rw [abs_mul]
      refine mul_le_mul ?_ (ih' _ _ _ h1 ((wt_erase_le σ k).trans h2)) (abs_nonneg _) hK
      exact_mod_cast abs_mult_k_le hn h2 (Multiset.mem_toFinset.1 hk)
    have b3 : ((#σ'.toFinset + #σ.toFinset : ℕ) : ℚ) ≤ 8 * h := by exact_mod_cast card_terms_le h1 h2
    calc _ ≤ #σ'.toFinset • (4 * h * 2 ^ (5 * h) * B) + #σ.toFinset • (4 * h * 2 ^ (5 * h) * B) := (abs_add_le _ _).trans (add_le_add b1 b2)
      _ = ((#σ'.toFinset + #σ.toFinset : ℕ) : ℚ) * (4 * h * 2 ^ (5 * h) * B) := by rw [nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
      _ ≤ 8 * h * (4 * h * 2 ^ (5 * h) * B) := mul_le_mul_of_nonneg_right b3 (mul_nonneg hK hB)
      _ = B * (32 * (h : ℚ) ^ 2 * 2 ^ (5 * h)) := by ring
end GeneralPieces.Sizes
