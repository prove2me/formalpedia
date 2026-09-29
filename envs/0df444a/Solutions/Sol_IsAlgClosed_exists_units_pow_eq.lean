-- Prove2me | solution 1 for IsAlgClosed.exists_units_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/10c2ce89-6a8b-5e84-b4f3-bf9bc5b7353d

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAlgClosed_exists_units_pow_eq

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem solution
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {n : ℕ} (hn : 0 < n) (x : Ωˣ) :
    ∃ y : Ωˣ, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : Ω) hn
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hz, zero_pow hn.ne'])
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

end S_IsAlgClosed_exists_units_pow_eq
end P2MW
export P2MW.S_IsAlgClosed_exists_units_pow_eq (solution)
