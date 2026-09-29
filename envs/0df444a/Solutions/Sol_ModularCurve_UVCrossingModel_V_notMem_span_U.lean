-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.V_notMem_span_U
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/41a39df6-465d-5b49-b8b1-49f71b3e593f

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_V_notMem_span_U

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    V π ∉ Ideal.span {U π} :=
  by
  obtain ⟨e, heV, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries π
  intro hmem
  apply PowerSeries.X_ne_zero (R := W ⧸ Ideal.span {π})
  rw [← heV, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

end S_ModularCurve_UVCrossingModel_V_notMem_span_U
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_V_notMem_span_U (solution)
