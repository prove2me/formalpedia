-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_0_residue_count__p2m_8f071b5d_2675_41bd_8723_304b8e6b90ee_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T11:36:23.419492+00:00
-- url     : https://prove2.me/submissions/433aa1c2-5d9f-4c5e-af27-815a492389a7

import Mathlib
import Theorems.Thm_KnodelPrimeCordial_count_selected_residue_one__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
import Theorems.Thm_KnodelPrimeCordial_count_selected_residue_two__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
import Theorems.Thm_KnodelPrimeCordial_count_selected_residue_four__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
import Theorems.Thm_KnodelPrimeCordial_count_selected_residue_partition__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1

theorem solution (n : ℕ) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)).card =
      (n + 2) / 4 := by
  let k := n / 12
  have hn : n = 12 * k + 6 := by
    dsimp [k]
    omega
  have hsize : n / 2 = 6 * k + 3 := by
    dsimp [k]
    omega
  have hcount :
      (Finset.univ.filter fun j : Fin (n / 2) =>
        j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)).card = 3 * k + 2 := by
    rw [hsize]
    rw [KnodelPrimeCordial.count_selected_residue_partition__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1]
    rw [KnodelPrimeCordial.count_selected_residue_one__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1]
    rw [KnodelPrimeCordial.count_selected_residue_two__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1]
    rw [KnodelPrimeCordial.count_selected_residue_four__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1]
    omega
  have hrhs : (n + 2) / 4 = 3 * k + 2 := by
    dsimp [k]
    omega
  exact hcount.trans hrhs.symm
