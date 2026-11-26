-- Prove2me | solution 1 for N4Code.min4_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:47.499661+00:00
-- url     : https://prove2.me/submissions/4a4bcf87-f072-40d8-8c80-32c597416fed

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_min4_eq_image

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution (a : Fin 4 → ℕ) (ρ : Equiv (Fin 4) (Fin 4)) :
    min (a (ρ 0)) (min (a (ρ 1)) (min (a (ρ 2)) (a (ρ 3)))) =
      min (a 0) (min (a 1) (min (a 2) (a 3))) := by
  calc
    min (a (ρ 0)) (min (a (ρ 1)) (min (a (ρ 2)) (a (ρ 3))))
        = (Finset.univ.image (fun j : Fin 4 => a (ρ j))).min' (by simp) :=
          min4_eq_image (fun j : Fin 4 => a (ρ j))
    _ = (Finset.univ.image a).min' (by simp) := by
          congr 1
          ext x
          constructor
          · intro hx
            rcases (Finset.mem_image.mp hx) with ⟨j, _hj, hjy⟩
            apply Finset.mem_image.mpr
            refine ⟨ρ j, ?_, hjy⟩
            simp
          · intro hy
            rcases (Finset.mem_image.mp hy) with ⟨k, _hk, hky⟩
            apply Finset.mem_image.mpr
            refine ⟨ρ.symm k, ?_, ?_⟩
            · simp
            · simpa using hky
    _ = min (a 0) (min (a 1) (min (a 2) (a 3))) := (min4_eq_image a).symm
end N4Code
