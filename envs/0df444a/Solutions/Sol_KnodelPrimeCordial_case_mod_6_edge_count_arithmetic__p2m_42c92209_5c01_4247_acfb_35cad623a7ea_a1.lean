-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_edge_count_arithmetic__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:10:20.115474+00:00
-- url     : https://prove2.me/submissions/c3c6b912-3455-4a5e-9c9c-e22c5c6867b2

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_count__p2m_09d5ad41_d63b_42b2_b02b_457801360f54_a1
open scoped BigOperators

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    ∑ k : Fin 3,
      (Finset.univ.filter fun j : Fin (n / 2) =>
        Nat.Coprime
          (KnodelPrimeCordial.labelF (2 * j.val))
          (KnodelPrimeCordial.labelF
            ((2 * ((j.val + 2 ^ k.val - 1) % (n / 2)) + n - 1) % n))).card =
      (3 * n + 2) / 4 := by
  classical
  have hc :=
    KnodelPrimeCordial.case_mod_6_offset_count__p2m_09d5ad41_d63b_42b2_b02b_457801360f54_a1
      n hn h10 hmod
  rw [Fin.sum_univ_three]
  rw [hc (0 : Fin 3), hc (1 : Fin 3), hc (2 : Fin 3)]
  norm_num
  omega
