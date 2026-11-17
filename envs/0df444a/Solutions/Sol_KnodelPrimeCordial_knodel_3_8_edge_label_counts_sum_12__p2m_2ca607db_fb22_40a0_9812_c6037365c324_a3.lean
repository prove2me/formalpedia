-- Prove2me | solution 1 for KnodelPrimeCordial.knodel_3_8_edge_label_counts_sum_12__p2m_2ca607db_fb22_40a0_9812_c6037365c324_a3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T09:47:10.143095+00:00
-- url     : https://prove2.me/submissions/f4cf9cb2-6d43-4a87-ad14-d2c4c2e08630

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_edge_gcd_positive_from_bij__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
import Theorems.Thm_KnodelPrimeCordial_edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
import Theorems.Thm_KnodelPrimeCordial_knodel_3_8_edge_count__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1

theorem solution
    (f : Fin 2 × Fin 4 → ℕ)
    (hbij : Set.BijOn f Set.univ (Set.Icc 1 8)) :
    (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 8) f).card +
      (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 8) f).card = 12 := by
  calc
    _ = (KnodelPrimeCordial.knodel 3 8).edgeFinset.card :=
      KnodelPrimeCordial.edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
        (KnodelPrimeCordial.knodel 3 8) f
        (KnodelPrimeCordial.edge_gcd_positive_from_bij__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
          f hbij)
    _ = 12 :=
      KnodelPrimeCordial.knodel_3_8_edge_count__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1

