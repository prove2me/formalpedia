-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_10__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:06:26.880144+00:00
-- url     : https://prove2.me/submissions/8cca3775-c48d-4401-8adb-74630a3148db

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
import Theorems.Thm_KnodelPrimeCordial_cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    KnodelPrimeCordial.PrimeCordial (KnodelPrimeCordial.knodel 3 n) := by
  obtain ⟨hbij, hbal⟩ :=
    KnodelPrimeCordial.cyclic_case_mod_10__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
      n hn h10 hmod
  let f : Fin n → ℕ := fun i =>
    if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val
  have hf : KnodelPrimeCordial.IsPrimeCordialLabeling (KnodelPrimeCordial.cyc n) f := by
    exact ⟨by simpa [f] using hbij, by simpa [f] using hbal⟩
  obtain ⟨g, hg⟩ :=
    KnodelPrimeCordial.cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
      n hn h10 f hf
  exact ⟨g, hg⟩
