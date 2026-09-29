-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.ringKrullDim_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c738151f-bdcc-5642-a2f7-246220432ede

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_ringKrullDim_eq_two

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] [IsNoetherianRing W] [IsLocalRing W] [IsDomain W] {π : W} (hW : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ0 : π ≠ 0) :
    ringKrullDim (UVCrossingModel W π) = 2 :=
  by

  haveI hmax : (Ideal.span {π}).IsMaximal := hW ▸ IsLocalRing.maximalIdeal.isMaximal W
  have hπu : ¬IsUnit π := by
    have : π ∈ IsLocalRing.maximalIdeal W := hW ▸ Ideal.mem_span_singleton_self π
    exact (IsLocalRing.mem_maximalIdeal _).mp this
  haveI : IsLocalRing (UVCrossingModel W π) := ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hπu
  haveI : IsNoetherianRing (UVCrossingModel W π) := ModularCurve.UVCrossingModel.isNoetherianRing π

  have hU0 : U π ∈ nonZeroDivisors (UVCrossingModel W π) :=
    ModularCurve.UVCrossingModel.U_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
  have hUm : U π ∈ IsLocalRing.maximalIdeal (UVCrossingModel W π) := by
    rw [ModularCurve.UVCrossingModel.maximalIdeal_eq_span_pair hW]
    exact Ideal.subset_span (Set.mem_insert _ _)

  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hU0 hUm
  letI : Field (W ⧸ Ideal.span {π}) := Ideal.Quotient.field (Ideal.span {π})
  obtain ⟨e, -, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries π
  have h1 : ringKrullDim (UVCrossingModel W π ⧸ Ideal.span {U π}) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one (PowerSeries (W ⧸ Ideal.span {π}))
  rw [← hdrop, h1]
  rfl

end S_ModularCurve_UVCrossingModel_ringKrullDim_eq_two
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_ringKrullDim_eq_two (solution)
