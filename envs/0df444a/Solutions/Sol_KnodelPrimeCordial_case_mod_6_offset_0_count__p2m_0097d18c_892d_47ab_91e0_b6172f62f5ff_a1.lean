-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_0_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:26:55.709722+00:00
-- url     : https://prove2.me/submissions/f6c3e946-44b1-4027-97ea-b19c07cf1f85

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_0_coprime_classification__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1

open scoped BigOperators

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 0 - 1) % (n / 2)) + n - 1) % n))).card =
      (n + 2) / 4 := by
  rw [← KnodelPrimeCordial.case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
    n hmod]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact KnodelPrimeCordial.case_mod_6_offset_0_coprime_classification__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
    n hmod j
