-- Prove2me | solution 1 for KnodelPrimeCordial.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T09:43:55.402368+00:00
-- url     : https://prove2.me/submissions/59878176-7e4e-449e-89ea-1e2696cfff6a

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel
import Theorems.Thm_KnodelPrimeCordial_case_mod_0__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_2__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_4__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_8__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_10__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) :
    KnodelPrimeCordial.PrimeCordial (KnodelPrimeCordial.knodel 3 n) := by
  have hnCopy := hn
  rcases hnCopy with ⟨k, hk⟩
  have hmod : n % 12 < 12 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 12
  · exact KnodelPrimeCordial.case_mod_0__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
      n hn h10 h
  · omega
  · exact KnodelPrimeCordial.case_mod_2__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
      n hn h10 h
  · omega
  · exact KnodelPrimeCordial.case_mod_4__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
      n hn h10 h
  · omega
  · exact KnodelPrimeCordial.case_mod_6__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
      n hn h10 h
  · omega
  · exact KnodelPrimeCordial.case_mod_8__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
      n hn h10 h
  · omega
  · exact KnodelPrimeCordial.case_mod_10__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
      n hn h10 h
  · omega
