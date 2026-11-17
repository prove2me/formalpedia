-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:12:57.099223+00:00
-- url     : https://prove2.me/submissions/fad9f30e-f05e-4a6c-aeb4-7e6e071698e4

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_mapsTo__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
import Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_injOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
import Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_surjOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.BijOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) := by
  exact ⟨
    KnodelPrimeCordial.labelF_mod_6_mapsTo__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
      n hn h10 hmod,
    KnodelPrimeCordial.labelF_mod_6_injOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
      n hn h10 hmod,
    KnodelPrimeCordial.labelF_mod_6_surjOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
      n hn h10 hmod⟩
