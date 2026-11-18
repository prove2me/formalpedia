-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:15:57.760864+00:00
-- url     : https://prove2.me/submissions/f8728c18-c6e0-483a-b771-0635d75c44b3

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_edge_balance__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    Set.BijOn
        (fun i : Fin n => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)
        Set.univ (Set.Icc 1 n) ∧
      |((KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
          (fun i : Fin n =>
            if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ) -
        ((KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
          (fun i : Fin n =>
            if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ)| ≤ 1 := by
  let g : Fin n → ℕ := fun i =>
    if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val
  have hbij := KnodelPrimeCordial.cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
    n hn h10 hmod
  have hbal := KnodelPrimeCordial.cyclic_case_mod_10_edge_balance__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
    n hn h10 hmod
  constructor
  · simpa [g] using hbij
  · simpa [g] using hbal
