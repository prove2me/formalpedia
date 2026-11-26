-- Prove2me | solution 1 for N4Code.lambda_diff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:49.640157+00:00
-- url     : https://prove2.me/submissions/3cd5640b-5beb-4792-8dff-5d57d3ef8116

import Definitions.Def_N4Code_Performance
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Comparison

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (_hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y)) (ε : ℝ) :
    lambda C' ε - lambda C ε =
      (1 / 4 : ℝ) * ∑ y ∈ S, (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
  unfold lambda
  rw [← mul_sub]
  congr 1
  calc
    (∑ y : Word n, weight n ε (dCode C' y)) - ∑ y : Word n, weight n ε (dCode C y)
        = ∑ y : Word n, (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
          have hgsum : (∑ y : Word n, weight n ε (dCode C' y)) =
              ∑ y : Word n, weight n ε (dCode C' (g y)) := by
            apply Finset.sum_bij (fun y _ => g.symm y)
            · intro y _; simp
            · intro a _ b _ hab
              exact g.symm.injective hab
            · intro b _
              refine ⟨g b, by simp, by simp⟩
            · intro y _; simp
          rw [hgsum, ← Finset.sum_sub_distrib]
    _ = ∑ y ∈ S, (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
          have hzero : ∀ y : Word n, y ∉ S →
              weight n ε (dCode C' (g y)) - weight n ε (dCode C y) = 0 := by
            intro y hy
            rw [heq y hy]
            ring
          symm
          apply Finset.sum_subset
          · intro y _; simp
          · intro y _ hy
            exact hzero y hy
end N4Code
