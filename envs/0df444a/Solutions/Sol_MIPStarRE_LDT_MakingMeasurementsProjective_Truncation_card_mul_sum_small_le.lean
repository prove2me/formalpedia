-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_mul_sum_small_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:34:22.598896+00:00
-- url     : https://prove2.me/submissions/9f15cbb5-0884-421b-8914-c748b2e11403

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.card_mul_sum_small_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution {α : Type*} {L S : Finset α}
    {f : α → ℝ} (hf : ∀ s ∈ S, ∀ l ∈ L, f s ≤ f l) :
    (L.card : ℝ) * (∑ s ∈ S, f s) ≤ (S.card : ℝ) * (∑ l ∈ L, f l) := by
  classical
  have hL :
      (L.card : ℝ) * (∑ s ∈ S, f s) = ∑ s ∈ S, ∑ _l ∈ L, f s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [Finset.sum_const, nsmul_eq_mul]
  have hR :
      (S.card : ℝ) * (∑ l ∈ L, f l) = ∑ l ∈ L, ∑ _s ∈ S, f l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro l hl
  refine Finset.sum_le_sum ?_
  intro s hs
  exact hf s hs l hl
end MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
