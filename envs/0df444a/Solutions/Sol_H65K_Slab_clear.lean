-- Prove2me | solution 1 for H65K.Slab.clear
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:47:17.702963+00:00
-- url     : https://prove2.me/submissions/33f7f00d-856d-477f-84d4-15bd8499d9f2

import Theorems.Thm_H65K_Slab_head
import Theorems.Thm_H65K_Slab_cell00
import Theorems.Thm_H65K_Slab_cell01
import Theorems.Thm_H65K_Slab_cell02
import Theorems.Thm_H65K_Slab_cell03
import Theorems.Thm_H65K_Slab_cell04
import Theorems.Thm_H65K_Slab_cell05
import Theorems.Thm_H65K_Slab_cell06
import Theorems.Thm_H65K_Slab_cell07
import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_Arb4_Q_cv_nat
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_add
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem solution :
    EdgeClearGlue.SlabClear (65000 : ℝ) ((65000 : ℝ) + 3 / 1000) := by
  have hcells : ∀ j, j < H65K.Slab.S.m → Arb4.cellOK H65K.Slab.S j = true := by
    intro j hj
    have hm : H65K.Slab.S.m = 8 := rfl
    rw [hm] at hj
    interval_cases j
    · exact H65K.Slab.cell00
    · exact H65K.Slab.cell01
    · exact H65K.Slab.cell02
    · exact H65K.Slab.cell03
    · exact H65K.Slab.cell04
    · exact H65K.Slab.cell05
    · exact H65K.Slab.cell06
    · exact H65K.Slab.cell07
  have hok : Arb4.slabOK H65K.Slab.S = true := by
    simp only [Arb4.slabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range]
    exact ⟨H65K.Slab.head, hcells⟩
  have h := Arb4.slabOK_sound H65K.Slab.S hok
  have hlo : H65K.Slab.S.lo.val = (65000 : ℝ) := Q.cv_nat 65000
  have hhi : H65K.Slab.S.hi.val = ((65000 : ℝ) + 3 / 1000) :=
    Q.cv_add _ _ _ _ (Q.cv_nat 65000) (Q.cv_frac 3 1000)
  rw [hlo, hhi] at h
  exact h
