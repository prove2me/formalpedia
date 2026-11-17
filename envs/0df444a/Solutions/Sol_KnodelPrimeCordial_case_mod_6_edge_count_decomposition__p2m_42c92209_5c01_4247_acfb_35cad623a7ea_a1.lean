-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_edge_count_decomposition__p2m_42c92209_5c01_4247_acfb_35cad623a7ea_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:11:04.044686+00:00
-- url     : https://prove2.me/submissions/6d09606d-85d4-427e-a84a-0e6e3801d77d

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_edge_count_by_offsets__p2m_8a6c92bd_7c8f_41ac_9c83_07dd1e357c6c_a1

open scoped BigOperators

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n)
      (fun v : Fin 2 × Fin (n / 2) =>
        KnodelPrimeCordial.labelF
          (if v.1 = 0 then (2 * v.2.val) % n
            else (2 * v.2.val + n - 1) % n))).card =
      ∑ k : Fin 3,
        (Finset.univ.filter fun j : Fin (n / 2) =>
          Nat.Coprime
            (KnodelPrimeCordial.labelF (2 * j.val))
            (KnodelPrimeCordial.labelF
              ((2 * ((j.val + 2 ^ k.val - 1) % (n / 2)) + n - 1) % n))).card := by
  rcases hn with ⟨m, hm⟩
  have hn2 : n = 2 * (n / 2) := by omega
  let f : Fin 2 × Fin (n / 2) → ℕ := fun v =>
    KnodelPrimeCordial.labelF
      (if v.1 = 0 then (2 * v.2.val) % n
        else (2 * v.2.val + n - 1) % n)
  have h4 : 4 ≤ n / 2 := by omega
  have hcount :=
    KnodelPrimeCordial.case_mod_6_edge_count_by_offsets__p2m_8a6c92bd_7c8f_41ac_9c83_07dd1e357c6c_a1
      n h4 f
  have hleft (j : Fin (n / 2)) : 2 * j.val < n := by omega
  have hleft_mod (j : Fin (n / 2)) : (2 * j.val) % n = 2 * j.val :=
    Nat.mod_eq_of_lt (hleft j)
  simpa [f, hleft_mod] using hcount
