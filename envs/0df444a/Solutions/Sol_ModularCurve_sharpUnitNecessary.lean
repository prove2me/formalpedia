-- Prove2me | solution 1 for ModularCurve.sharpUnitNecessary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3c87edca-22f7-5ed7-b7d0-12aad6eba588

import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_prime
import Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sharpUnitNecessary

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.SharpUnitNecessary ℓ := by
  by_cases h : ℓ % 12 = 1
  · exact ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one ℓ h
  · exact ModularCurve.sharpUnitNecessary_of_prime ℓ h

end S_ModularCurve_sharpUnitNecessary
end P2MW
export P2MW.S_ModularCurve_sharpUnitNecessary (solution)
