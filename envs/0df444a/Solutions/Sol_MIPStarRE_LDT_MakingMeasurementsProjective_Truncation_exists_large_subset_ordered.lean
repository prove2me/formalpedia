-- Prove2me | solution 1 for MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:34:11.658853+00:00
-- url     : https://prove2.me/submissions/7b06d3d9-ea30-46e3-992a-c637f20d546f

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/TruncationCombinatorics.lean (solution of MIPStarRE.LDT.MakingMeasurementsProjective.Truncation.exists_large_subset_ordered);
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
theorem _root_.solution {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {d : ℕ} (hd : d ≤ Fintype.card α) :
    ∃ L : Finset α, L.card = d ∧
      ∀ s ∈ (Lᶜ : Finset α), ∀ l ∈ L, f s ≤ f l := by
  classical
  let candidates : Finset (Finset α) := (Finset.univ : Finset α).powersetCard d
  have hcandidates : candidates.Nonempty := by
    simpa [candidates] using
      (Finset.powersetCard_nonempty_of_le (s := (Finset.univ : Finset α)) hd)
  obtain ⟨L, hLmem, hLmax⟩ :=
    Finset.exists_max_image candidates (fun T : Finset α => ∑ x ∈ T, f x) hcandidates
  have hL_card : L.card = d := (Finset.mem_powersetCard.mp hLmem).2
  refine ⟨L, hL_card, ?_⟩
  intro s hs l hl
  by_contra hnot
  have hlt : f l < f s := lt_of_not_ge hnot
  have hs_not_mem : s ∉ L := by
    simpa using hs
  let L' : Finset α := insert s (L.erase l)
  have hL'_card : L'.card = d := by
    have hs_erase : s ∉ L.erase l := fun hs' => hs_not_mem (Finset.mem_of_mem_erase hs')
    have hcard_erase : (L.erase l).card = d - 1 := by
      rw [Finset.card_erase_of_mem hl, hL_card]
    have hd_pos : 0 < d := by
      rw [← hL_card]
      exact Finset.card_pos.mpr ⟨l, hl⟩
    calc
      L'.card = (L.erase l).card + 1 := by rw [Finset.card_insert_of_notMem hs_erase]
      _ = d := by omega
  have hL'_mem : L' ∈ candidates := by
    rw [Finset.mem_powersetCard]
    exact ⟨by intro x hx; simp, hL'_card⟩
  have hsum_L' : ∑ x ∈ L', f x = (∑ x ∈ L, f x) - f l + f s := by
    have hs_erase : s ∉ L.erase l := fun hs' => hs_not_mem (Finset.mem_of_mem_erase hs')
    have hsum_erase : ∑ x ∈ L.erase l, f x = (∑ x ∈ L, f x) - f l := by
      have h := Finset.add_sum_erase L f hl
      linarith
    calc
      ∑ x ∈ L', f x = f s + ∑ x ∈ L.erase l, f x := by
        simp [L', hs_erase]
      _ = (∑ x ∈ L, f x) - f l + f s := by
        rw [hsum_erase]
        ring
  have hstrict : (∑ x ∈ L, f x) < ∑ x ∈ L', f x := by
    rw [hsum_L']
    linarith
  exact not_lt_of_ge (hLmax L' hL'_mem) hstrict
end MIPStarRE.LDT.MakingMeasurementsProjective.Truncation
