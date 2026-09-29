-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.U_notMem_span_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c8792d2a-eda4-5408-9119-5f126e5be0e9

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_U_notMem_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    U π ∉ Ideal.span {V π} :=
  by
  obtain ⟨e, heU, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries π
  intro hmem
  apply PowerSeries.X_ne_zero (R := W ⧸ Ideal.span {π})
  rw [← heU, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

end S_ModularCurve_UVCrossingModel_U_notMem_span_V
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_U_notMem_span_V (solution)
