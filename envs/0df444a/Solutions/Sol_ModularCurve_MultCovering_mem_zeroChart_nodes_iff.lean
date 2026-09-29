-- Prove2me | solution 1 for ModularCurve.MultCovering.mem_zeroChart_nodes_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/03548889-acde-50ec-b0e4-70ce4254bc52

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_mem_zeroChart_nodes_iff

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (x : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
    x ∈ (zeroChart Γ).nodes ↔
      ∃ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p) = x := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  rw [show (zeroChart Γ).nodes = Γ.Wn from rfl,
    ← PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply,
    PlaceSpecialization.LevelOneProlongationPair.mem_chartFst_nodes_iff]
  constructor
  · rintro ⟨b, hb, hbx⟩
    refine ⟨b ^ p, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p b).mpr hb, ?_⟩
    rw [← pow_mul, ← sq, Γ.supply.pow_sq_eq_self_of_mem b hb]; exact hbx
  · rintro ⟨a, ha, hax⟩
    exact ⟨a ^ p, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p a).mpr ha, hax⟩

end S_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
end P2MW
export P2MW.S_ModularCurve_MultCovering_mem_zeroChart_nodes_iff (solution)
