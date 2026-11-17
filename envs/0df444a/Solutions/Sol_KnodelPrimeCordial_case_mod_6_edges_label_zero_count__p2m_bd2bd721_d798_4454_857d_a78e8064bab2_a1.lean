-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_edges_label_zero_count__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:54:41.754079+00:00
-- url     : https://prove2.me/submissions/7556db56-e957-42cc-adaa-22bd2c64185e

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_edge_one_count__p2m_a2d2c024_75ef_4507_a500_d8ffa22c501d_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 n)
      (fun v : Fin 2 × Fin (n / 2) =>
        KnodelPrimeCordial.labelF
          (if v.1 = 0 then (2 * v.2.val) % n
            else (2 * v.2.val + n - 1) % n))).card = (3 * n - 2) / 4 := by
  have hsum :=
    KnodelPrimeCordial.case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
      n hn h10 hmod
  have hone :=
    KnodelPrimeCordial.case_mod_6_label_edge_one_count__p2m_a2d2c024_75ef_4507_a500_d8ffa22c501d_a1
      n hn h10 hmod
  omega
