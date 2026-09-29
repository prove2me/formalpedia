-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isIntegrallyClosed_sections_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/87e39b46-8f47-5fc4-85fc-85c6030c98fc

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_sections_of_isAffineOpen

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (U : (ModularCurve.IgusaScheme N ℓ).Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed ↑Γ(ModularCurve.IgusaScheme N ℓ, U) :=
  AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen
    (↥(GaloisRep.ratLocalizedAt ℓ)) (↥(modularFunctionFieldFull N)) (jFull N) U hU

end S_ModularCurve_IgusaScheme_isIntegrallyClosed_sections_of_isAffineOpen
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_sections_of_isAffineOpen (solution)
