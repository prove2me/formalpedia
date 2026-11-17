-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_2_count__p2m_0097d18c_892d_47ab_91e0_b6172f62f5ff_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:32:13.83057+00:00
-- url     : https://prove2.me/submissions/d10e9289-b4d2-4f1d-a8c4-abf64cd03428

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_0_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_1_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_2_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_3_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_4_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_5_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_assembly__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
open scoped BigOperators

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card =
      (n + 2) / 4 := by
  apply KnodelPrimeCordial.case_mod_6_offset_2_residue_assembly__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
    n hn h10 hmod
  · exact KnodelPrimeCordial.case_mod_6_offset_2_residue_0_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
      n hn h10 hmod
  · exact KnodelPrimeCordial.case_mod_6_offset_2_residue_1_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
      n hn h10 hmod
  · exact KnodelPrimeCordial.case_mod_6_offset_2_residue_2_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
      n hn h10 hmod
  · exact KnodelPrimeCordial.case_mod_6_offset_2_residue_3_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
      n hn h10 hmod
  · exact KnodelPrimeCordial.case_mod_6_offset_2_residue_4_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
      n hn h10 hmod
  · exact KnodelPrimeCordial.case_mod_6_offset_2_residue_5_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
      n hn h10 hmod
