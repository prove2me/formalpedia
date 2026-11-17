-- Prove2me | solution 1 for KnodelPrimeCordial.count_selected_residue_four__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T13:07:56.56983+00:00
-- url     : https://prove2.me/submissions/0b057b7d-a994-4b30-8114-27b78774162a

import Mathlib

theorem solution (k : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 4).card = k := by
  classical
  let P : Fin (6 * k + 3) → Prop := fun j => j.val ≠ 0 ∧ j.val % 6 = 4
  let e : {j : Fin (6 * k + 3) // P j} ≃ Fin k :=
    { toFun := fun j =>
        (⟨j.1.val / 6, by
          have hb : j.1.val < 6 * k + 3 := j.1.isLt
          have hm : j.1.val % 6 = 4 := j.2.2
          have hd := Nat.mod_add_div j.1.val 6
          omega⟩ : Fin k)
      invFun := fun i =>
        (⟨(⟨6 * i.val + 4, by
            have hi : i.val < k := i.isLt
            omega⟩ : Fin (6 * k + 3)), by
          change 6 * i.val + 4 ≠ 0 ∧ (6 * i.val + 4) % 6 = 4
          omega⟩ : {j : Fin (6 * k + 3) // P j})
      left_inv := fun j => by
        apply Subtype.ext
        apply Fin.ext
        change 6 * (j.1.val / 6) + 4 = j.1.val
        have hd := Nat.mod_add_div j.1.val 6
        rw [j.2.2] at hd
        omega
      right_inv := fun i => by
        apply Fin.ext
        change (6 * i.val + 4) / 6 = i.val
        omega }
  have hcard : Fintype.card {j : Fin (6 * k + 3) // P j} = Fintype.card (Fin k) :=
    Fintype.card_congr e
  rw [Fintype.card_subtype] at hcard
  simpa [P] using hcard
