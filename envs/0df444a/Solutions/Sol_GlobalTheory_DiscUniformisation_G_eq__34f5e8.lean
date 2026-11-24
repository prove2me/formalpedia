-- Prove2me | solution 1 for GlobalTheory.DiscUniformisation.G_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:23:47.53636+00:00
-- url     : https://prove2.me/submissions/8422b778-ff6d-4cae-98f7-aab2c8c1d6ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution (L : PeriodPair) (z : ℍ) (hz : L.ω₁ = L.ω₂ * z) {k : ℕ} (hk : 3 ≤ k) :
    L.G k = (L.ω₂⁻¹) ^ k * (2 * riemannZeta k * E hk z) := by
  have hE : E hk z = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 (k : ℤ) z := rfl
  calc L.G k = ∑' v : Fin 2 → ℤ, (L.ω₂⁻¹) ^ k * EisensteinSeries.eisSummand k v z := by
        unfold PeriodPair.G
        rw [← (L.latticeEquivProd.symm.toEquiv).tsum_eq, ← (finTwoArrowEquiv ℤ).tsum_eq]
        congr 1
        funext v
        simp only [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply, finTwoArrowEquiv_apply,
          EisensteinSeries.eisSummand, zpow_natCast]
        have e : (v 0 : ℂ) * L.ω₁ + v 1 * L.ω₂ = L.ω₂ * (v 0 * z + v 1) := by rw [hz]; ring
        show (((v 0 : ℂ) * L.ω₁ + (v 1 : ℂ) * L.ω₂) ^ k)⁻¹ = _
        rw [e, mul_pow, mul_inv, inv_pow]
        congr 1
        try simp [one_div]
    _ = (L.ω₂⁻¹) ^ k * (riemannZeta k * eisensteinSeries (N := 1) 0 (k : ℤ) z) := by
        rw [tsum_mul_left, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z]
    _ = _ := by rw [hE]; ring
end GlobalTheory.DiscUniformisation
