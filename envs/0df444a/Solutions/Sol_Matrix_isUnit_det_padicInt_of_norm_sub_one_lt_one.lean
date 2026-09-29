-- Prove2me | solution 1 for Matrix.isUnit_det_padicInt_of_norm_sub_one_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3be516de-d460-5d7d-a95b-084f28184eb3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one

set_option maxHeartbeats 8000000
open Matrix

theorem solution
    (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Matrix (Fin n) (Fin n) ℤ_[p])
    (h : ∀ i j, ‖P i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) :
    IsUnit P.det := by
  classical

  have htz : ∀ x : ℤ_[p], ‖x‖ < 1 → (PadicInt.toZMod : ℤ_[p] →+* ZMod p) x = 0 := fun x hx => by
    obtain ⟨y, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp hx
    rw [map_mul, show ((p : ℤ_[p]) = ((p:ℕ) : ℤ_[p])) from rfl, map_natCast,
        ZMod.natCast_self, zero_mul]

  have hmapeq : (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix P
      = (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix (1:Matrix (Fin n) (Fin n) ℤ_[p]) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub]
    exact htz _ (h i j)
  have hdet1 : (PadicInt.toZMod : ℤ_[p] →+* ZMod p) P.det = 1 := by
    rw [RingHom.map_det, hmapeq, map_one, Matrix.det_one]

  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  push_neg at hlt
  exact zero_ne_one (α := ZMod p) ((htz P.det hlt) ▸ hdet1)

end S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one
end P2MW
export P2MW.S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one (solution)
