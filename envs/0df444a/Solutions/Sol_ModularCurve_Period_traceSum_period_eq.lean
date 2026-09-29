-- Prove2me | solution 1 for ModularCurve.Period.traceSum_period_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cdf11dcc-0ac5-53e7-bbdc-f7a298c53cf2

import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodTransfer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_traceSum_period_eq

set_option autoImplicit false

open scoped MatrixGroups

open ModularCurve.Period

theorem solution :
    ∀ {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
      {F : UpperHalfPlane → ℂ} [inst : Fintype (↥Γ ⧸ Δ.subgroupOf Γ)]
      (hF : ModularCurve.Period.IsEquivariantPrimitive Δ F) (γ : ↥Γ),
      (ModularCurve.Period.IsEquivariantPrimitive.traceSum hF).period γ =
        ∑ q, hF.period (ModularCurve.Period.transferElt γ q) := by
  intro Γ Δ F inst hF γ
  rw [← IsEquivariantPrimitive.sub_eq_period hF.traceSum γ UpperHalfPlane.I]
  exact sum_traceRep_smul_sub hF γ UpperHalfPlane.I

#print axioms solution

end S_ModularCurve_Period_traceSum_period_eq
end P2MW
export P2MW.S_ModularCurve_Period_traceSum_period_eq (solution)
