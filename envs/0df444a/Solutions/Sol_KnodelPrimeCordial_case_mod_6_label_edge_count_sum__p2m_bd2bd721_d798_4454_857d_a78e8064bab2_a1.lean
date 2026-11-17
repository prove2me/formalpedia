-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:53:29.176243+00:00
-- url     : https://prove2.me/submissions/e3e98516-abaf-41d7-a723-e706ee2cc6a7

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_gcd_positive__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_edge_count__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 n)
          (fun v : Fin 2 × Fin (n / 2) =>
            KnodelPrimeCordial.labelF
              (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card +
        (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n)
          (fun v : Fin 2 × Fin (n / 2) =>
            KnodelPrimeCordial.labelF
              (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card =
      3 * n / 2 := by
  let f : Fin 2 × Fin (n / 2) → ℕ := fun v =>
    KnodelPrimeCordial.labelF
      (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
  have hpos : ∀ e ∈ (KnodelPrimeCordial.knodel 3 n).edgeFinset,
      0 < KnodelPrimeCordial.edgeGcd f e :=
    KnodelPrimeCordial.case_mod_6_label_gcd_positive__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
      n hn h10 hmod
  have hpart :=
    KnodelPrimeCordial.edge_label_partition__p2m_730717b0_dc72_4b0f_b59f_ead0370cbb16_a1
      (KnodelPrimeCordial.knodel 3 n) f hpos
  have hcard : (KnodelPrimeCordial.knodel 3 n).edgeFinset.card = 3 * n / 2 :=
    KnodelPrimeCordial.case_mod_6_edge_count__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
      n hn h10 hmod
  simpa [f] using hpart.trans hcard
