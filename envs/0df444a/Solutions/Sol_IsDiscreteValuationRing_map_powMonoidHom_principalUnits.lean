-- Prove2me | solution 1 for IsDiscreteValuationRing.map_powMonoidHom_principalUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f7d2a3d8-51c8-59ab-a4cb-1a6c86624cd5

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsLocalRing_pow_mem_principalUnits
import Theorems.Thm_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_map_powMonoidHom_principalUnits

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : Ideal.span {(p : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) :
    (principalUnits R k).map (powMonoidHom p) = principalUnits R (k + e) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    have hpe' : (p : R) ∈ IsLocalRing.maximalIdeal R ^ e := by
      rw [← hpe]; exact Ideal.mem_span_singleton_self _
    have h := IsLocalRing.pow_mem_principalUnits hp hpe' hu
    have hmin : k + e ≤ min (p * k) (k + e) := by
      refine le_min ?_ le_rfl
      calc k + e ≤ k + k := by omega
        _ = 2 * k := (two_mul k).symm
        _ ≤ p * k := Nat.mul_le_mul_right k hp.two_le
    exact principalUnits_antitone hmin h
  · intro w hw
    obtain ⟨u, hu, huw⟩ := IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq hp.pos hpe hk hw
    exact ⟨u, hu, huw⟩

end S_IsDiscreteValuationRing_map_powMonoidHom_principalUnits
end P2MW
export P2MW.S_IsDiscreteValuationRing_map_powMonoidHom_principalUnits (solution)
