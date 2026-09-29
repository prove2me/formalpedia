-- Prove2me | solution 1 for ModularCurve.MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ed1fdb20-2b84-5845-90ba-0cfc9075196e

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (he0 : ssValue Γ e ≠ 0) (he1728 : ssValue Γ e ≠ 1728) :
    ∃ u : ↥A, IsUnit u ∧ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u := by
  refine ⟨1, isUnit_one, ?_⟩
  show ((Δ.An e).modulus : AlgebraicClosure ℚ) = _
  rw [Δ.modulus_eq e, jWidth_of_ne he0 he1728]; push_cast; ring

end S_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne
end P2MW
export P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne (solution)
