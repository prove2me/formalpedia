-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.crossingSwap_chartHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4b8c0dd7-ea66-5fa7-b7a7-48e7dba6001d

import Definitions.Def_ModularCurve_UVCrossingChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_chartHom

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) (f : PowerSeries W) :
    crossingSwap π (chartHom π f) = chartHom π f :=
  by
  have hsw : ∀ f : PowerSeries W, uvSwapEquiv (PowerSeries.subst (sAmbient W) f) = PowerSeries.subst (sAmbient W) f := by
    intro f
    rw [uvSwapEquiv_apply, MvPowerSeries.rename_eq_subst, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply
        (PowerSeries.HasSubst.const (hasSubst_sAmbient W))
        (MvPowerSeries.HasSubst.X_comp _)]
    have h : (fun _ : Unit ↦ MvPowerSeries.subst
        (MvPowerSeries.X ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) (sAmbient W)) =
        (fun _ : Unit ↦ sAmbient W) := by
      funext _
      rw [← MvPowerSeries.rename_eq_subst, ← uvSwapEquiv_apply]
      rw [sAmbient, map_add, uvSwapEquiv_X_zero, uvSwapEquiv_X_one, add_comm]
    rw [h, ← PowerSeries.subst_def]
  rw [chartHom_apply, crossingSwap_mk, hsw]

end S_ModularCurve_UVCrossingModel_crossingSwap_chartHom
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_chartHom (solution)
