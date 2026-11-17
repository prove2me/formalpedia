-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_label_bijective__p2m_585db7c0_0954_404f_a5c5_92bed9ed7485_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:29:39.597348+00:00
-- url     : https://prove2.me/submissions/d135ce45-5da2-4cd7-9661-76d27fb6be63

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_pair_index_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
import Theorems.Thm_KnodelPrimeCordial_labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.BijOn
      (fun v : Fin 2 × Fin (n / 2) =>
        KnodelPrimeCordial.labelF
          (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))
      Set.univ (Set.Icc 1 n) := by
  let idx : Fin 2 × Fin (n / 2) → ℕ := fun v =>
    if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n
  have hidx : Set.BijOn idx Set.univ (Set.Icc 0 (n - 1)) :=
    KnodelPrimeCordial.pair_index_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
      n hn h10 hmod
  have hlabel : Set.BijOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) :=
    KnodelPrimeCordial.labelF_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
      n hn h10 hmod
  change Set.BijOn (fun v => KnodelPrimeCordial.labelF (idx v)) Set.univ (Set.Icc 1 n)
  exact hlabel.comp hidx
