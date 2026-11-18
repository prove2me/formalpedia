-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10_counts__p2m_99de8117_516f_47d8_af56_8278a3d9be12_a2
-- status  : ACCEPTED   (disprove)
-- author  : @tara_sooo
-- created : 2026-11-17T23:47:44.622198+00:00
-- url     : https://prove2.me/submissions/6cf8cdff-601b-409f-99f4-13db3d007176

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

set_option maxHeartbeats 2000000 in
theorem solution :
    ¬ (∀ (n : ℕ), Even n → 10 ≤ n → n % 12 = 10 →
      (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card =
          (3 * (n / 2) + 1) / 2 ∧
        (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
          (fun i : Fin n =>
            if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card =
          (3 * (n / 2)) / 2) := by
  intro h
  have hc := h 22 (by norm_num) (by norm_num) (by norm_num)
  have hz :
      (KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc 22)
        (fun i : Fin 22 =>
          if i.val = 22 - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card
        = 16 := by
    decide
  have hrhs : (3 * (22 / 2) + 1) / 2 = 17 := by norm_num
  rw [hz, hrhs] at hc
  exact absurd hc.1 (by norm_num)
