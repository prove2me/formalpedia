-- Prove2me | solution 1 for Matrix.isUnit_of_isUnit_map_of_le_jacobson_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f347d4aa-5136-525c-afdb-7e37b5be569b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot

set_option autoImplicit false

universe u v

theorem solution
    {S : Type u} [CommRing S] {n : Type v} [Fintype n] [DecidableEq n]
    (𝔫 : Ideal S) (h𝔫 : 𝔫 ≤ (⊥ : Ideal S).jacobson)
    (A : Matrix n n S) (hA : IsUnit (A.map (Ideal.Quotient.mk 𝔫))) :
    IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hA

  obtain ⟨b, hb⟩ := hA.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔫), Ideal.Quotient.eq] at hb
  have hu : IsUnit (A.det * b) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (h𝔫 hb)
  exact isUnit_of_mul_isUnit_left hu

end S_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot
end P2MW
export P2MW.S_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot (solution)
