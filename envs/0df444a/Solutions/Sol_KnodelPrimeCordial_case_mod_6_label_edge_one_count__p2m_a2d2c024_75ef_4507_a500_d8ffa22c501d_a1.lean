-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_label_edge_one_count__p2m_a2d2c024_75ef_4507_a500_d8ffa22c501d_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:03:28.999209+00:00
-- url     : https://prove2.me/submissions/391f8468-0e14-4085-8c47-0a4d6bfc1897

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_edge_count_decomposition__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_edge_count_arithmetic__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1

open scoped BigOperators

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n)
      (fun v : Fin 2 × Fin (n / 2) =>
        KnodelPrimeCordial.labelF
          (if v.1 = 0 then (2 * v.2.val) % n
            else (2 * v.2.val + n - 1) % n))).card = (3 * n + 2) / 4 := by
  calc
    _ = ∑ k : Fin 3,
          (Finset.univ.filter fun j : Fin (n / 2) =>
            Nat.Coprime
              (KnodelPrimeCordial.labelF (2 * j.val))
              (KnodelPrimeCordial.labelF
                ((2 * ((j.val + 2 ^ k.val - 1) % (n / 2)) + n - 1) % n))).card :=
      KnodelPrimeCordial.case_mod_6_edge_count_decomposition__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
        n hn h10 hmod
    _ = (3 * n + 2) / 4 :=
      KnodelPrimeCordial.case_mod_6_edge_count_arithmetic__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
        n hn h10 hmod
