-- Prove2me | solution 1 for LinearMap.charpoly_eq_iff_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5f78c23a-064a-5d75-9f75-3be1d1b3f971

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Theorems.Thm_LinearMap_charpoly_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_charpoly_eq_iff_of_finrank_eq_two

open Polynomial

theorem solution {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) (a b : R) : f.charpoly = X ^ 2 - C a * X + C b ↔ LinearMap.trace R M f = a ∧ LinearMap.det f = b := by
  rw [LinearMap.charpoly_of_finrank_eq_two h f]
  constructor
  · intro he
    have h0 := congr_arg (fun q : R[X] ↦ q.coeff 0) he
    have h1 := congr_arg (fun q : R[X] ↦ q.coeff 1) he
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at h0 h1
    norm_num at h0 h1
    exact ⟨h1, h0⟩
  · rintro ⟨ht, hd⟩
    rw [ht, hd]

end S_LinearMap_charpoly_eq_iff_of_finrank_eq_two
end P2MW
export P2MW.S_LinearMap_charpoly_eq_iff_of_finrank_eq_two (solution)
