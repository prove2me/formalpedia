-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_univ_mul_sum_compl_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:35:18.583556+00:00
-- url     : https://prove2.me/submissions/44a40f2c-f4e1-400d-a44f-cc0d5ff35c6a

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_univ_mul_sum_compl_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_Truncation_card_mul_sum_small_le

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (L : Finset α) {f : α → ℝ}
    (hf : ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l) :
    (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) ≤
      (Lᶜ.card : ℝ) * (∑ x, f x) := by
  classical
  have hcard_nat : L.card + Lᶜ.card = Fintype.card α := Finset.card_add_card_compl L
  have hcard : (Fintype.card α : ℝ) = (L.card : ℝ) + (Lᶜ.card : ℝ) := by
    exact_mod_cast hcard_nat.symm
  have hunion : ∑ x, f x = (∑ l ∈ L, f l) + ∑ s ∈ (Lᶜ : Finset α), f s := by
    have := Finset.sum_add_sum_compl (s := L) (f := f)
    linarith
  have hbase := card_mul_sum_small_le (L := L) (S := (Lᶜ : Finset α)) (f := f) hf
  calc
    (Fintype.card α : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s)
        = ((L.card : ℝ) + (Lᶜ.card : ℝ)) * (∑ s ∈ (Lᶜ : Finset α), f s) := by
              rw [hcard]
    _ = (L.card : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) +
          (Lᶜ.card : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) := by ring
    _ ≤ (Lᶜ.card : ℝ) * (∑ l ∈ L, f l) +
          (Lᶜ.card : ℝ) * (∑ s ∈ (Lᶜ : Finset α), f s) := by
              linarith [hbase]
    _ = (Lᶜ.card : ℝ) * ((∑ l ∈ L, f l) + ∑ s ∈ (Lᶜ : Finset α), f s) := by ring
    _ = (Lᶜ.card : ℝ) * (∑ x, f x) := by rw [← hunion]
end MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
