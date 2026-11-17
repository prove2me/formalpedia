-- Prove2me | solution 1 for KnodelPrimeCordial.cyclic_case_mod_10_bijective__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:25:22.58691+00:00
-- url     : https://prove2.me/submissions/14f1e00d-26f5-4087-9d98-24f31fe40ff7

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_label_range__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_label_injective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
import Theorems.Thm_KnodelPrimeCordial_cyclic_case_mod_10_label_surjective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    Set.BijOn
      (fun i : Fin n => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)
      Set.univ (Set.Icc 1 n) := by
  let f : Fin n → ℕ :=
    fun i => if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val
  have hrange :=
    KnodelPrimeCordial.cyclic_case_mod_10_label_range__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
      n hn h10 hmod
  have hinj :=
    KnodelPrimeCordial.cyclic_case_mod_10_label_injective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
      n hn h10 hmod
  have hsurj :=
    KnodelPrimeCordial.cyclic_case_mod_10_label_surjective__p2m_6dfc39c6_04b4_4470_a7a0_9be6cdfdbf5c_a1
      n hn h10 hmod
  change Set.MapsTo f Set.univ (Set.Icc 1 n) ∧
    Set.InjOn f Set.univ ∧ Set.SurjOn f Set.univ (Set.Icc 1 n)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hrange i
  · intro i hi j hj hij
    exact hinj hij
  · intro y hy
    obtain ⟨i, hiy⟩ := hsurj y hy
    exact ⟨i, Set.mem_univ i, hiy⟩
