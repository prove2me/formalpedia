-- Prove2me | solution 1 for ModularCurve.heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6260c1f6-b559-53ea-ba4d-9a540c2d1650

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorModL
import Theorems.Thm_ModularCurve_frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (x : JZeroC K N) (hx : (ℓ : ℤ) • x = 0) :
    heckeOperatorModL K N ℓ x = frobeniusPushforwardModL K N ℓ x := by
  rw [heckeOperatorModL_apply, frobeniusPullbackModL_eq_zero_of_natCast_smul_eq_zero K ℓ N x hx, add_zero]

end S_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero
end P2MW
export P2MW.S_ModularCurve_heckeOperatorModL_eq_frobeniusPushforwardModL_of_natCast_smul_eq_zero (solution)
