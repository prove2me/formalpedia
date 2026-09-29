-- Prove2me | solution 1 for ModularCurve.MultCovering.infChart_def
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e0003fbe-8311-5d2a-9b52-a010a10536c3

import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_infChart_def

set_option autoImplicit false

open AlgebraicCurve ModularCurve.MultCovering

set_option maxHeartbeats 3200000 in
theorem solution {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    infChart Γ = ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply := rfl

end S_ModularCurve_MultCovering_infChart_def
end P2MW
export P2MW.S_ModularCurve_MultCovering_infChart_def (solution)
