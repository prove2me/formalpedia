-- Prove2me | solution 1 for ModularCurve.MultCovering.AnnCtx.exists_mem_pow_modulusExp_eq_modulus_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/61a4ba88-fed7-5b39-b5b5-31fe02c26fea

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_mem_pow_modulusExp_eq_modulus_mul
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    (p : AlgebraicClosure ℚ) ^ modulusExp = ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * a := by
  intro e
  have hmod : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show ((Δ.An e).modulus : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  have hle : jWidth (ssValue Γ e) ≤ 3 := by
    rcases jWidth_eq_one_or (ssValue Γ e) with h | h | h <;> omega
  refine ⟨(p : AlgebraicClosure ℚ) ^ (3 - jWidth (ssValue Γ e)), pow_mem (natCast_mem A p) _, ?_⟩
  rw [hmod, ← pow_add, Nat.add_sub_cancel' hle]
  rfl

end S_ModularCurve_MultCovering_AnnCtx_exists_mem_pow_modulusExp_eq_modulus_mul
end P2MW
export P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_mem_pow_modulusExp_eq_modulus_mul (solution)
