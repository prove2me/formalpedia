-- Prove2me | solution 1 for KnodelPrimeCordial.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T09:43:20.478299+00:00
-- url     : https://prove2.me/submissions/c1032aa7-a6e9-4c47-9d34-e290107e4ff2

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_knodel_3_8_edge_label_counts_sum_12__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3
import Theorems.Thm_KnodelPrimeCordial_knodel_3_8_coprime_edge_lower_bound__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3

open KnodelPrimeCordial

theorem solution : ¬ PrimeCordial (knodel 3 8) := by
  rintro ⟨f, ⟨hbij, hbal⟩⟩
  let z := (edgesLabelZero (knodel 3 8) f).card
  let o := (edgesLabelOne (knodel 3 8) f).card
  have hsum : z + o = 12 := by
    dsimp [z, o]
    exact KnodelPrimeCordial.knodel_3_8_edge_label_counts_sum_12__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3 f hbij
  have hlarge : 7 ≤ o := by
    dsimp [o]
    exact KnodelPrimeCordial.knodel_3_8_coprime_edge_lower_bound__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3 f hbij
  have hsumZ : (z : ℤ) + (o : ℤ) = 12 := by exact_mod_cast hsum
  have habs := abs_le.mp hbal
  have hdiff1 : (z : ℤ) - (o : ℤ) ≤ 1 := habs.2
  have hdiff2 : (o : ℤ) - (z : ℤ) ≤ 1 := by linarith [habs.1]
  have ho : o = 6 := by omega
  omega
