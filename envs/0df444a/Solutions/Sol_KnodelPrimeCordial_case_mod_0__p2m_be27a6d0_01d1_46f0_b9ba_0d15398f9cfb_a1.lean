-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_0__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-18T01:01:34.750204+00:00
-- url     : https://prove2.me/submissions/e738ea38-28da-40f6-9bb7-1f47837d0c56

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_0_cyc_cordial
import Theorems.Thm_KnodelPrimeCordial_cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 0) :
    KnodelPrimeCordial.PrimeCordial (KnodelPrimeCordial.knodel 3 n) := by
  have hpos : 0 < n := by omega
  have h12 : 12 ∣ n := ⟨n / 12, by omega⟩
  have hcyc :=
    KnodelPrimeCordial.case_mod_0_cyc_cordial n hpos h12
  obtain ⟨g, hg⟩ :=
    KnodelPrimeCordial.cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
      n hn h10 (fun i : Fin n => KnodelPrimeCordial.labelF i.val) hcyc
  exact ⟨g, hg⟩
