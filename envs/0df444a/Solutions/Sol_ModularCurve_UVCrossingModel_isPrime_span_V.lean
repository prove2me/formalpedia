-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.isPrime_span_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/60928635-2e53-56fc-a0c7-13c155d4a0bd

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isDomain_quotient_span_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_isPrime_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] :
    (Ideal.span {V π}).IsPrime :=
  by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact ModularCurve.UVCrossingModel.isDomain_quotient_span_V π

end S_ModularCurve_UVCrossingModel_isPrime_span_V
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_isPrime_span_V (solution)
