-- Prove2me | solution 1 for IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ba7ab596-74f5-5a43-926c-5622bccf1f15

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsIntegrallyClosed_of_faithfullyFlat
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
set_option autoImplicit false

open ModularCurve

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* UVCrossingModel W (π ^ E)) :
    IsIntegrallyClosed R := by
  obtain ⟨hdom, -, hic⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE
  haveI : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    MulEquiv.isDomain (UVCrossingModel W (π ^ E)) ι.toMulEquiv
  haveI : IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsIntegrallyClosed.of_equiv ι.symm
  haveI : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  exact IsIntegrallyClosed.of_faithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R)

end S_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
end P2MW
export P2MW.S_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel (solution)
