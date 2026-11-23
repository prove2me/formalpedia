-- Prove2me | solution 1 for ManipPotential.proposition_6_12_no_transfer_path_switch
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:41:51.633164+00:00
-- url     : https://prove2.me/submissions/0e4f7a98-de6a-41b0-aa98-9adbab88d07f

import Mathlib
import Definitions.Def_ManipPotential_TransferStep
import Definitions.Def_ManipPotential_BoundedMP

theorem solution {m : ℕ} (K : ℕ)
    (g : (ManipPotential.Ranking m → ℚ) → Fin m) (hg : ManipPotential.BoundedMP K g)
    (i j : Fin m) (hij : i ≠ j) (L : ℕ) (Q : ℕ → ManipPotential.Ranking m → ℚ)
    (hstart : g (Q 0) = i) (hend : g (Q L) = j)
    (hwinners : ∀ k ≤ L, g (Q k) = i ∨ g (Q k) = j)
    (hsteps : ∀ k < L, ManipPotential.TransferStep K i j (Q k) (Q (k + 1))) : False := by
  have no_switch (A B : ManipPotential.Ranking m → ℚ) (hA : g A = i) (hB : g B = j)
      (hstep : ManipPotential.TransferStep K i j A B) : False := by
    obtain ⟨r, s, a, ha, hcase⟩ := hstep
    have hlam : (0 : ℚ) < (K : ℚ) + 1 := by positivity
    have hlama : (0 : ℚ) < ((K : ℚ) + 1) * a := mul_pos hlam ha
    rcases hcase with ⟨hrij, hBmove, hP⟩ | ⟨hrji, hBmove, hP⟩
    · let P := A - a • ManipPotential.unitVec s
      have hAform : A = P + a • ManipPotential.unitVec s := by
        dsimp [P]
        abel
      have hBform : B = P + (((K : ℚ) + 1) * a) • ManipPotential.unitVec r := by
        rw [hBmove]
        dsimp [P]
        module
      have hcomp := hg P hP r s (((K : ℚ) + 1) * a) a hlama ha (le_refl _)
      rw [← hBform, ← hAform, hB, hA] at hcomp
      exact (not_le_of_gt hrij) hcomp
    · let P := A - a • ((K : ℚ) + 1) • ManipPotential.unitVec r
      have hAform : A = P + (((K : ℚ) + 1) * a) • ManipPotential.unitVec r := by
        dsimp [P]
        module
      have hBform : B = P + a • ManipPotential.unitVec s := by
        rw [hBmove]
        dsimp [P]
        module
      have hcomp := hg P hP r s (((K : ℚ) + 1) * a) a hlama ha (le_refl _)
      rw [← hAform, ← hBform, hA, hB] at hcomp
      exact (not_le_of_gt hrji) hcomp
  have all_i : ∀ k ≤ L, g (Q k) = i := by
    intro k
    induction k with
    | zero => intro _; exact hstart
    | succ k ih =>
        intro hk
        have hk' : k < L := by omega
        have hprev : g (Q k) = i := ih (by omega)
        rcases hwinners (k + 1) hk with hnext | hnext
        · exact hnext
        · exact (no_switch (Q k) (Q (k + 1)) hprev hnext
            (hsteps k hk')).elim
  exact hij ((all_i L (le_refl L)).symm.trans hend)
