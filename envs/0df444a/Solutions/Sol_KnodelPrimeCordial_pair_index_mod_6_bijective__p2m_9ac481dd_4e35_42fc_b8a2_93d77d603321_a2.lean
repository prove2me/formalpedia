-- Prove2me | solution 1 for KnodelPrimeCordial.pair_index_mod_6_bijective__p2m_9ac481dd_4e35_42fc_b8a2_93d77d603321_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:42:08.719618+00:00
-- url     : https://prove2.me/submissions/a62850df-e266-41a5-9a9f-72994a6d3234

import Mathlib
import Theorems.Thm_KnodelPrimeCordial_pair_index_mod_6_injective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1
import Theorems.Thm_KnodelPrimeCordial_pair_index_mod_6_surjective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.BijOn
      (fun v : Fin 2 × Fin (n / 2) =>
        if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)
      Set.univ (Set.Icc 0 (n - 1)) := by
  refine ⟨?_,
    KnodelPrimeCordial.pair_index_mod_6_injective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1
      n hn h10 hmod,
    KnodelPrimeCordial.pair_index_mod_6_surjective__p2m_ae6d8231_810e_48e1_8a23_71cafce1ec8b_a1
      n hn h10 hmod⟩
  intro v hv
  simp only [Set.mem_Icc]
  constructor
  · exact Nat.zero_le _
  · have hpos : 0 < n := by omega
    have hlt :
        (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n) < n := by
      split_ifs <;> exact Nat.mod_lt _ hpos
    omega
