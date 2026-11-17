-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_three_regular_side0__p2m_9dfa4dbf_1cc5_4722_9f1c_fa72524f7381_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:37:27.990454+00:00
-- url     : https://prove2.me/submissions/926bf0af-e30a-4053-905a-2cbcb92a43cb

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_knodel_three_neighborFinset__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
import Theorems.Thm_KnodelPrimeCordial_knodel_three_offsets_distinct__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) :
    (KnodelPrimeCordial.knodel 3 n).degree (0, j) = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [KnodelPrimeCordial.knodel_three_neighborFinset__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
    n hn h10 j]
  obtain ⟨hxy, hxz, hyz⟩ :=
    KnodelPrimeCordial.knodel_three_offsets_distinct__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
      n hn h10 j
  simp [hxy, hxz, hyz]
