-- Prove2me | solution 1 for ModularCurve.heckeDivBar_comm_of_heckeExchangeAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/19dda9de-c5e9-55d7-8bc8-d807c43b0765

import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_heckeDivBar_heckeDivBar_of_heckeExchangeAt
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_congr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {N ℓ ℓ' M : ℕ} [NeZero N] [NeZero ℓ] [NeZero ℓ'] [NeZero M] (hM : M = N * ℓ * ℓ') (hM' : M = N * ℓ' * ℓ) (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ) (hα' : HeckeAlphaBarIntegral L N ℓ') (hβ' : HeckeBetaBarIntegral L N ℓ') [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))] [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ')))] [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull M))] (hu : (towerInclBar L (dvd_of_eq_roof N ℓ ℓ' M hM).1).toRingHom.IsIntegral) (hu' : (towerSubstBar L (N * ℓ') ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).2).toRingHom.IsIntegral) (hv : (towerInclBar L (dvd_of_eq_roof N ℓ' ℓ M hM').1).toRingHom.IsIntegral) (hv' : (towerSubstBar L (N * ℓ) ℓ' (dvd_of_eq_roof N ℓ' ℓ M hM').2).toRingHom.IsIntegral) (hex : HeckeExchangeAt L N ℓ ℓ' M hM) (hex' : HeckeExchangeAt L N ℓ' ℓ M hM') (D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) : heckeDivBar hα hβ (heckeDivBar hα' hβ' D) = heckeDivBar hα' hβ' (heckeDivBar hα hβ D) := by
  have h₁ : N * (ℓ * ℓ') ∣ M := ⟨1, by rw [hM]; ring⟩
  have h₁' : N * (ℓ' * ℓ) ∣ M := ⟨1, by rw [hM]; ring⟩
  have h₂ : N ∣ M := ⟨ℓ * ℓ', by rw [hM]; ring⟩
  have hs : (towerSubstBar L N (ℓ * ℓ') h₁).toRingHom.IsIntegral := by
    rw [← towerSubstBar_comp_heckeBetaBar L ℓ ℓ' (dvd_of_eq_roof N ℓ ℓ' M hM).2 h₁]
    exact RingHom.IsIntegral.trans _ _ hβ' hu'
  have hs' : (towerSubstBar L N (ℓ' * ℓ) h₁').toRingHom.IsIntegral := by
    rw [← towerSubstBar_comp_heckeBetaBar L ℓ' ℓ (dvd_of_eq_roof N ℓ' ℓ M hM').2 h₁']
    exact RingHom.IsIntegral.trans _ _ hβ hv'
  have hi : (towerInclBar L h₂).toRingHom.IsIntegral := by
    rw [← towerInclBar_comp_heckeAlphaBar L ℓ (dvd_of_eq_roof N ℓ ℓ' M hM).1 h₂]
    exact RingHom.IsIntegral.trans _ _ hα hu
  rw [ModularCurve.heckeDivBar_heckeDivBar_of_heckeExchangeAt L hM hα hβ hα' hβ' hu hu' h₁ h₂ hs hi hex D,
    ModularCurve.heckeDivBar_heckeDivBar_of_heckeExchangeAt L hM' hα' hβ' hα hβ hv hv' h₁' h₂ hs' hi hex' D]
  exact AlgebraicCurve.Divisor.correspondence_congr (towerSubstBar_congr L (mul_comm ℓ ℓ') h₁ h₁') rfl _ _ _ _ D

end S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt
end P2MW
export P2MW.S_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt (solution)
