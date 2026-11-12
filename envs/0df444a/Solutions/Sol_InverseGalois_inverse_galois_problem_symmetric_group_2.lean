-- Prove2me | solution 2 for InverseGalois.inverse_galois_problem_symmetric_group
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-15T20:29:21.553522+00:00
-- url     : https://prove2.me/submissions/03037f96-6f48-4d1d-b051-61484fd46443
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InverseGalois_realizability
import Theorems.Thm_InverseGalois_generic_inverse_galois_symmetric
import Theorems.Thm_InverseGalois_hilbert_descent_multivariate

open InverseGalois

theorem solution {S : Type*} [Fintype S] : IsRealizable ℚ (Equiv.Perm S) := by
  classical
  have h1 := generic_inverse_galois_symmetric (S := Fin (Fintype.card S))
  have h2 : IsRealizable ℚ (Equiv.Perm (Fin (Fintype.card S))) :=
    hilbert_descent_multivariate h1
  obtain ⟨r⟩ := h2.exists_realization
  exact ⟨⟨{ L := r.L
            to_field := r.to_field
            to_algebra := r.to_algebra
            to_isGalois := r.to_isGalois
            iso := (Equiv.permCongrHom (Fintype.equivFin S)).trans r.iso }⟩⟩
