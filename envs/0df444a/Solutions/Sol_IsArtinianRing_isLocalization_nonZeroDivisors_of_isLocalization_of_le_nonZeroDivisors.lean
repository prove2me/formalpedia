-- Prove2me | solution 1 for IsArtinianRing.isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/74ffc0db-84ce-5535-866f-d0d277c69af8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {B F : Type*} [CommRing B] [CommRing F] [Algebra B F]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M F] [IsArtinianRing F] :
    IsLocalization (nonZeroDivisors B) F := by
  refine IsLocalization.of_le M (nonZeroDivisors B) hM fun r hr => ?_
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro u hu
  obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective M u
  have h1 : algebraMap B F (x * r) = 0 := by
    have h := congrArg (fun z => z * algebraMap B F (m : B)) hu
    simp only [zero_mul] at h
    rw [map_mul, ← IsLocalization.mk'_spec F x m]
    calc IsLocalization.mk' F x m * algebraMap B F ↑m * algebraMap B F r
        = IsLocalization.mk' F x m * algebraMap B F r * algebraMap B F ↑m := by ring
      _ = 0 := h
  obtain ⟨m', hm'⟩ := (IsLocalization.map_eq_zero_iff M F _).1 h1
  have hx : (m' : B) * x = 0 := by
    have h2 : (m' : B) * x * r = 0 := by rw [mul_assoc]; exact hm'
    exact (mem_nonZeroDivisors_iff_right.1 hr) _ h2
  exact (IsLocalization.mk'_eq_zero_iff x m).2 ⟨m', hx⟩

end S_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors
end P2MW
export P2MW.S_IsArtinianRing_isLocalization_nonZeroDivisors_of_isLocalization_of_le_nonZeroDivisors (solution)
