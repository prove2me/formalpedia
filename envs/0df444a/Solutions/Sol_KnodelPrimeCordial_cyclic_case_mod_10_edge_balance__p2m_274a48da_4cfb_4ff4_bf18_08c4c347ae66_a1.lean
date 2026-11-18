-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10_edge_balance__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-17T17:05:20.469301+00:00
-- url     : https://prove2.me/submissions/bd1ec76d-4311-4f18-a962-33428e470046
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_counts__p2m_99de8117_516f_47d8_af56_8278a3d9be12_a2

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    |((KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ) -
      ((KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ)| ≤ 1 := by
  obtain ⟨hzero, hone⟩ :=
    KnodelPrimeCordial.cyclic_case_mod_10_counts__p2m_99de8117_516f_47d8_af56_8278a3d9be12_a2
      n hn h10 hmod
  rw [hzero, hone]
  have hhalf : n / 2 = 6 * (n / 12) + 5 := by omega
  have hzero_count : (3 * (n / 2) + 1) / 2 = 9 * (n / 12) + 8 := by omega
  have hone_count : (3 * (n / 2)) / 2 = 9 * (n / 12) + 7 := by omega
  rw [hzero_count, hone_count]
  have hdiff :
      ((9 * (n / 12) + 8 : ℕ) : ℤ) - ((9 * (n / 12) + 7 : ℕ) : ℤ) = 1 := by
    push_cast
    omega
  rw [hdiff]
  norm_num
