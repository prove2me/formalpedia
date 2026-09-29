-- Prove2me | solution 1 for ModularCurve.deg_qInftyPlaceRat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4319e319-cfbd-559d-9e6c-1a652c5af462

import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_deg_of_toValuationSubring_eq_qIntegersBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deg_qInftyPlaceRat

open ModularCurve AlgebraicCurve

theorem solution {F : IntermediateField ℚ (LaurentSeries ℚ)} (h : ∃ j : F, (qSeriesBar ℚ F j).order = -1) : (qInftyPlaceRat F h).deg = 1 :=
  ModularCurve.deg_of_toValuationSubring_eq_qIntegersBar h _ rfl

end S_ModularCurve_deg_qInftyPlaceRat
end P2MW
export P2MW.S_ModularCurve_deg_qInftyPlaceRat (solution)
