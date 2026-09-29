-- Prove2me | solution 1 for ModularCurve.sum_inv_jWidth_of_ssJSetHasse
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6a2e2370-789a-53cf-bfd8-fff7eb49b578

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_sum_inv_jWidth_of_deuringPolynomial
import Theorems.Thm_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse

set_option autoImplicit false

open Polynomial ModularCurve Finset

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] [DecidableEq K] (S : Finset K)
    (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    ∑ j ∈ S, ((jWidth j : ℚ))⁻¹ = ((q : ℚ) - 1) / 12 := by
  have hq2 : q ≠ 2 := by omega
  have hSZ : S = ((Polynomial.deuringPolynomial q).map (Int.castRingHom K)).roots.toFinset.image
      legendreJ := by
    ext j
    rw [hS, ssJSetHasse_eq_image_legendreJ_toFinset q hq2 K, ← Finset.coe_image, Finset.mem_coe]
  rw [hSZ]
  exact sum_inv_jWidth_of_deuringPolynomial q hq K

end S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse
end P2MW
export P2MW.S_ModularCurve_sum_inv_jWidth_of_ssJSetHasse (solution)
