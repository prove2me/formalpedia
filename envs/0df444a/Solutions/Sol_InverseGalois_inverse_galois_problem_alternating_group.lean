-- Prove2me | solution 1 for InverseGalois.inverse_galois_problem_alternating_group
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T17:39:55.5797+00:00
-- url     : https://prove2.me/submissions/b3d0af4e-9f66-4d39-8f6c-aee009a4b2d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InverseGalois_inverse_galois_problem_hilbert_descent
import Theorems.Thm_InverseGalois_regular_inverse_galois_alternating

open InverseGalois

theorem solution (n : ℕ) :
    IsRealizable ℚ (alternatingGroup (Fin n)) := by
  classical
  exact inverse_galois_problem_hilbert_descent (regular_inverse_galois_alternating n)
