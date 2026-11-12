-- Prove2me | solution 1 for InverseGalois.inverse_galois_problem_symmetric_group
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T17:29:08.121898+00:00
-- url     : https://prove2.me/submissions/7f8a32be-dd91-4172-945d-6c63b3a89993
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InverseGalois_inverse_galois_problem_hilbert_descent
import Theorems.Thm_InverseGalois_regular_inverse_galois_symmetric

open InverseGalois

theorem solution {S : Type*} [Fintype S] :
    IsRealizable ℚ (Equiv.Perm S) := by
  classical
  exact inverse_galois_problem_hilbert_descent regular_inverse_galois_symmetric
