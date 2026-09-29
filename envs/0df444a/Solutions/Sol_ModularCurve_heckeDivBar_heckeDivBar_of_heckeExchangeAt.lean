-- Prove2me | solution 1 for ModularCurve.heckeDivBar_heckeDivBar_of_heckeExchangeAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5895cfd9-ceb7-5e53-8d1e-0e770063b869

import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_congr
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {N ℓ ℓ' M : ℕ} [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] (hM : M = N * ℓ * ℓ') (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) (hα' : HeckeAlphaBarIntegral L N ℓ') (hβ' : HeckeBetaBarIntegral L N ℓ') [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))] [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))] (hu : (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1).toRingHom.IsIntegral) (hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).toRingHom.IsIntegral) (h₁ : N * (ℓ * ℓ') ∣ M) (h₂ : N ∣ M) (hs : (towerSubstBar L N (ℓ * ℓ') h₁).toRingHom.IsIntegral) (hi : (towerInclBar L h₂).toRingHom.IsIntegral) (hex : HeckeExchangeAt L N ℓ ℓ' M hM) (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) : heckeDivBar hα hβ (heckeDivBar hα' hβ' D) = Divisor.correspondence (towerSubstBar L N (ℓ * ℓ') h₁) (towerInclBar L h₂) hs hi D := by
  rw [heckeDivBar, heckeDivBar,
    AlgebraicCurve.Divisor.correspondence_correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ)
      (heckeBetaBar L N ℓ') (heckeAlphaBar L N ℓ') (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1)
      (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2) hβ hα hβ' hα' hu hu'
      (RingHom.IsIntegral.trans _ _ hβ' hu') (RingHom.IsIntegral.trans _ _ hα hu)
      (fun D => hex hβ hα' hu hu' D) D]
  exact AlgebraicCurve.Divisor.correspondence_congr
    (towerSubstBar_comp_heckeBetaBar L ℓ ℓ' _ h₁) (towerInclBar_comp_heckeAlphaBar L ℓ _ h₂) _ _ _ _ D

end S_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt
end P2MW
export P2MW.S_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt (solution)
