-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_2_residue_1_index_count__p2m_da97d3f1_256c_4f52_83d8_9a648f286d22_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T13:02:56.549418+00:00
-- url     : https://prove2.me/submissions/a07c5a79-d59d-49cb-b36b-e8424b3b6279

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem count_fin_residue_one_local (q : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * q + 3) => j.val % 6 = 1).card = q + 1 := by
  let f : Fin (q + 1) → Fin (6 * q + 3) := fun t =>
    ⟨6 * t.val + 1, by have ht := t.isLt; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [f] at hv
    omega
  have hset :
      (Finset.univ.filter fun j : Fin (6 * q + 3) => j.val % 6 = 1) =
        Finset.univ.image f := by
    ext j
    constructor
    · intro hj
      have hmod : j.val % 6 = 1 := (Finset.mem_filter.mp hj).2
      rw [Finset.mem_image]
      refine ⟨⟨j.val / 6, ?_⟩, Finset.mem_univ _, ?_⟩
      · have hd : j.val % 6 + 6 * (j.val / 6) = j.val := Nat.mod_add_div _ _
        have hjlt := j.isLt
        omega
      · apply Fin.ext
        have hd : j.val % 6 + 6 * (j.val / 6) = j.val := Nat.mod_add_div _ _
        dsimp [f]
        omega
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨t, ht, hEq⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hval := congrArg Fin.val hEq
      dsimp [f] at hval
      have hm : (6 * t.val + 1) % 6 = 1 := by simp
      rw [← hval]
      exact hm
  rw [hset, Finset.card_image_iff.mpr (by
    intro a ha b hb hab
    exact hf hab)]
  simp

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = 1).card = n / 12 + 1 := by
  have hd : n % 12 + 12 * (n / 12) = n := Nat.mod_add_div _ _
  have hsize : n / 2 = 6 * (n / 12) + 3 := by omega
  rw [hsize]
  exact count_fin_residue_one_local (n / 12)
