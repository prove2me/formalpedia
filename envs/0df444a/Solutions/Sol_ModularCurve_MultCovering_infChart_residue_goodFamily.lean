-- Prove2me | solution 1 for ModularCurve.MultCovering.infChart_residue_goodFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/80ae0b99-acf5-5b82-b538-a63197dad55d

import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_infChart_residue_goodFamily

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers,
      (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩ = 1) ∧
      ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          (P l).natDegree + 1 ≤ mAnnuli p ∧
          (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩
            = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
        Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
          = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) :=
  Φ.t_inf A hA Γ

end S_ModularCurve_MultCovering_infChart_residue_goodFamily
end P2MW
export P2MW.S_ModularCurve_MultCovering_infChart_residue_goodFamily (solution)
