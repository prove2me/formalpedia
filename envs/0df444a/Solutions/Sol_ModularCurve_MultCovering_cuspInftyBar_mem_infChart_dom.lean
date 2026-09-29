-- Prove2me | solution 1 for ModularCurve.MultCovering.cuspInftyBar_mem_infChart_dom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3baab7bb-a9cf-5a0a-a543-972ffdee0842

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    cuspInftyBar (1 * p) ∈ (infChart Γ).dom :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply

end S_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom
end P2MW
export P2MW.S_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom (solution)
