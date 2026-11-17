-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_label_edge_counts__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:46:15.269687+00:00
-- url     : https://prove2.me/submissions/2db5e707-5695-4440-a7f9-8993bde9c989

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_edges_label_zero_count__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 n)
      (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF
        (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card =
        (3 * n - 2) / 4 ∧
      (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n)
      (fun v : Fin 2 × Fin (n / 2) => KnodelPrimeCordial.labelF
        (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))).card =
        (3 * n + 2) / 4 := by
  let f : Fin 2 × Fin (n / 2) → ℕ := fun v => KnodelPrimeCordial.labelF
    (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
  let z := (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.knodel 3 n) f).card
  let o := (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n) f).card
  have hz : z = (3 * n - 2) / 4 := by
    simpa [z, f] using
      KnodelPrimeCordial.case_mod_6_edges_label_zero_count__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
        n hn h10 hmod
  have hs : z + o = 3 * n / 2 := by
    simpa [z, o, f] using
      KnodelPrimeCordial.case_mod_6_label_edge_count_sum__p2m_bd2bd721_d798_4454_857d_a78e8064bab2_a1
        n hn h10 hmod
  let k := n / 12
  have hnrepr : n = 12 * k + 6 := by
    dsimp [k]
    omega
  have hzeroDiv : (3 * n - 2) / 4 = 9 * k + 4 := by
    rw [hnrepr]
    omega
  have honeDiv : (3 * n + 2) / 4 = 9 * k + 5 := by
    rw [hnrepr]
    omega
  have htotalDiv : 3 * n / 2 = 18 * k + 9 := by
    rw [hnrepr]
    omega
  have hz' : z = 9 * k + 4 := by rw [hz, hzeroDiv]
  have hs' : z + o = 18 * k + 9 := by rw [hs, htotalDiv]
  have hone : o = (3 * n + 2) / 4 := by
    rw [honeDiv]
    omega
  constructor
  · simpa [z, f] using hz
  · simpa [o, f] using hone
