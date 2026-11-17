-- Prove2me | solution 1 for KnodelPrimeCordial.labelF_mod_6_surjOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:21:57.353468+00:00
-- url     : https://prove2.me/submissions/de04b048-d296-478f-af40-8ea141dd2c61

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.SurjOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) := by
  exact (KnodelPrimeCordial.labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
    n hn h10 hmod).2.2
