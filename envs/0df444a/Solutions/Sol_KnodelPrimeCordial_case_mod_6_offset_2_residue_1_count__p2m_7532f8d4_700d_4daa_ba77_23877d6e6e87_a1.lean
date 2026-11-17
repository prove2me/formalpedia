-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_2_residue_1_count__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:40:51.80393+00:00
-- url     : https://prove2.me/submissions/2381179a-81a7-47b3-b8ee-50c6f7db1f58

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_1_pointwise_coprime__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
import Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_1_index_count__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 1 ∧
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12 + 1 := by
  classical
  have hcop : ∀ j : Fin (n / 2), j.val % 6 = 1 →
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n)) := by
    intro j hj
    exact KnodelPrimeCordial.case_mod_6_offset_2_residue_1_pointwise_coprime__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
      n hn h10 hmod j hj
  have hcount := KnodelPrimeCordial.case_mod_6_offset_2_residue_1_index_count__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
    n hn h10 hmod
  have hsets :
      (Finset.univ.filter fun j : Fin (n / 2) =>
        j.val % 6 = 1 ∧
        Nat.Coprime
          (KnodelPrimeCordial.labelF (2 * j.val))
          (KnodelPrimeCordial.labelF
            ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))) =
      (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = 1) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, _⟩
      exact hj
    · intro hj
      exact ⟨hj, hcop j hj⟩
  rw [hsets, hcount]
