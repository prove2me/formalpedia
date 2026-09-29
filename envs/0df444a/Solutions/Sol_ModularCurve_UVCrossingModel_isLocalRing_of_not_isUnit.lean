-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/df1cd901-f7bf-54bb-8878-59ecec865771

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_nontrivial_of_not_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit

open ModularCurve ModularCurve.UVCrossingModel

theorem solution {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hπ : ¬IsUnit π) :
    IsLocalRing (UVCrossingModel W π) :=
  by
  haveI : Nontrivial (UVCrossingModel W π) := ModularCurve.UVCrossingModel.nontrivial_of_not_isUnit hπ
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (uvCrossingIdeal W π))
    Ideal.Quotient.mk_surjective

end S_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit (solution)
