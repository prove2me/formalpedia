-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_2_residue_5_label_values__p2m_44d4bacb_229b_4cd5_be6a_4744e1588199_a1
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-16T15:38:08.041195+00:00
-- url     : https://prove2.me/submissions/025e83ee-f88c-49d4-9651-5c83ae23329d

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem solution : ¬ (∀ (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6)
    (j : Fin (n / 2)) (hj : j.val % 6 = 5),
    KnodelPrimeCordial.labelF (2 * j.val) = 2 * j.val + 2 ∧
      KnodelPrimeCordial.labelF
        ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n) = 2 * j.val + 3 ∧
      Nat.Coprime (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2) + n - 1) % n)))) := by
  intro H
  have h := (H 66 ⟨33, by norm_num⟩ (by norm_num) (by norm_num) ⟨29, by norm_num⟩ (by norm_num)).2.2
  have e1 : KnodelPrimeCordial.labelF (2 * 29) = 60 := by decide
  have e2 : KnodelPrimeCordial.labelF ((2 * ((29 + 2 ^ 2 - 1) % (66 / 2) + 66 - 1) % 66)) = 65 := by decide
  simp only [e1, e2] at h
  revert h
  decide
