-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_quotient_span_V
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/97287959-a613-575b-89c7-86d354dd9530

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_map_crossingSwap_span_U
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_quotient_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    ∃ e : (UVCrossingModel W π ⧸ Ideal.span {U π}) ≃+* (UVCrossingModel W π ⧸ Ideal.span {V π}), ∀ x : UVCrossingModel W π, e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (crossingSwap π x) :=
  ⟨Ideal.quotientEquiv (Ideal.span {U π}) (Ideal.span {V π}) (crossingSwap π)
    (ModularCurve.UVCrossingModel.map_crossingSwap_span_U π).symm, fun _ => rfl⟩

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_quotient_span_V
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_quotient_span_V (solution)
