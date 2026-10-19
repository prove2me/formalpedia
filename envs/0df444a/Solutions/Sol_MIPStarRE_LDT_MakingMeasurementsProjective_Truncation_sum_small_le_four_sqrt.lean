-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:36:05.553153+00:00
-- url     : https://prove2.me/submissions/631cc680-dc88-4d73-84b8-7676e244608c

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.sum_small_le_four_sqrt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_Truncation_card_univ_mul_sum_compl_le

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (L : Finset α)
    {f : α → ℝ}
    {d : ℕ} {ζ : ℝ}
    (hL_card : L.card = d)
    (hcard_gt : d < Fintype.card α)
    (hr_bound : (Fintype.card α : ℝ) ≤ (1 + 2 * Real.sqrt ζ) * d)
    (hf_ordering : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l)
    (htotal : (∑ x, f x) ≤ 1 + 2 * Real.sqrt ζ)
    (hζ_nonneg : 0 ≤ ζ)
    (hζ_le : ζ ≤ 1 / 4) :
    (∑ s ∈ (Lᶜ : Finset α), f s) ≤ 4 * Real.sqrt ζ := by
  classical
  have hr_pos : 0 < Fintype.card α := lt_of_le_of_lt (Nat.zero_le _) hcard_gt
  have hsqrt_nonneg : 0 ≤ Real.sqrt ζ := Real.sqrt_nonneg _
  have hsqrt_le_half : Real.sqrt ζ ≤ 1 / 2 := by
    have h1 : Real.sqrt ζ ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hζ_le
    have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  have hLc_card_nat : L.card + Lᶜ.card = Fintype.card α := Finset.card_add_card_compl L
  have hLc_card : (Lᶜ.card : ℝ) = (Fintype.card α : ℝ) - d := by
    have h1 : (L.card : ℝ) + (Lᶜ.card : ℝ) = (Fintype.card α : ℝ) := by
      exact_mod_cast hLc_card_nat
    have hL : (L.card : ℝ) = (d : ℝ) := by exact_mod_cast hL_card
    linarith
  have hLc_nonneg : (0 : ℝ) ≤ (Lᶜ.card : ℝ) := by exact_mod_cast Nat.zero_le _
  have hpart := card_univ_mul_sum_compl_le (α := α) L hf_ordering
  have hr_real_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hr_pos
  have htotal_nonneg : 0 ≤ 1 + 2 * Real.sqrt ζ := by positivity
  have hSsum_le_frac : ∑ s ∈ (Lᶜ : Finset α), f s ≤
      (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) * (1 + 2 * Real.sqrt ζ) := by
    have hrhs :
        (Lᶜ.card : ℝ) * (∑ x, f x) ≤
          (Lᶜ.card : ℝ) * (1 + 2 * Real.sqrt ζ) :=
      mul_le_mul_of_nonneg_left htotal hLc_nonneg
    have hcomb :
        (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) ≤
          (Lᶜ.card : ℝ) * (1 + 2 * Real.sqrt ζ) := le_trans hpart hrhs
    have hgoal_rewrite :
        (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) * (1 + 2 * Real.sqrt ζ) =
          (Lᶜ.card : ℝ) * (1 + 2 * Real.sqrt ζ) / (Fintype.card α : ℝ) := by ring
    rw [hgoal_rewrite, le_div_iff₀ hr_real_pos]
    nlinarith [hcomb]
  have hd_le_r : (d : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast (le_of_lt hcard_gt)
  have hLc_le : (Lᶜ.card : ℝ) ≤ 2 * Real.sqrt ζ * (Fintype.card α : ℝ) := by
    have h1 : (Fintype.card α : ℝ) - d ≤ 2 * Real.sqrt ζ * d := by
      nlinarith [hr_bound, hsqrt_nonneg]
    have h2 : 2 * Real.sqrt ζ * (d : ℝ) ≤ 2 * Real.sqrt ζ * (Fintype.card α : ℝ) := by
      nlinarith [hd_le_r, hsqrt_nonneg]
    linarith [hLc_card]
  have hratio : (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) ≤ 2 * Real.sqrt ζ := by
    rw [div_le_iff₀ hr_real_pos]
    linarith
  have hbound_final :
      (Lᶜ.card : ℝ) / (Fintype.card α : ℝ) * (1 + 2 * Real.sqrt ζ) ≤
        2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) :=
    mul_le_mul_of_nonneg_right hratio htotal_nonneg
  have hSsum_le_mix : ∑ s ∈ (Lᶜ : Finset α), f s ≤
      2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) := le_trans hSsum_le_frac hbound_final
  have hsq_sqrt : Real.sqrt ζ * Real.sqrt ζ = ζ := Real.mul_self_sqrt hζ_nonneg
  have h_4zeta_le_sqrt : 4 * ζ ≤ 2 * Real.sqrt ζ := by
    have h1 : 2 * (Real.sqrt ζ * Real.sqrt ζ) ≤ Real.sqrt ζ := by
      nlinarith [hsqrt_le_half, hsqrt_nonneg]
    calc 4 * ζ = 4 * (Real.sqrt ζ * Real.sqrt ζ) := by rw [hsq_sqrt]
      _ = 2 * (2 * (Real.sqrt ζ * Real.sqrt ζ)) := by ring
      _ ≤ 2 * Real.sqrt ζ := by linarith
  have h_rhs_expand :
      2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) = 2 * Real.sqrt ζ + 4 * ζ := by
    have hstep : 2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) =
        2 * Real.sqrt ζ + 4 * (Real.sqrt ζ * Real.sqrt ζ) := by ring
    rw [hstep, hsq_sqrt]
  have hfinal : 2 * Real.sqrt ζ * (1 + 2 * Real.sqrt ζ) ≤ 4 * Real.sqrt ζ := by
    rw [h_rhs_expand]; linarith
  exact le_trans hSsum_le_mix hfinal
end MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
