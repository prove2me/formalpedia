-- Prove2me | solution 1 for GlobalTheory.sum_coeff_mul_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:24.913803+00:00
-- url     : https://prove2.me/submissions/c57b6a2f-425a-449e-8916-eac93e3c906f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ColValueMulOfDisjointColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k σ : Type} [CommRing k] (w : (σ →₀ ℕ) → k) (P₁ P₂ : MvPolynomial σ k) :
    ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * w mo =
      ∑ m₁ ∈ P₁.support, ∑ m₂ ∈ P₂.support, P₁.coeff m₁ * P₂.coeff m₂ * w (m₁ + m₂) := by
  let L : MvPolynomial σ k →ₗ[k] k := (MvPolynomial.basisMonomials σ k).constr k w
  have hL : ∀ (m : σ →₀ ℕ) (a : k), L (MvPolynomial.monomial m a) = a * w m := by
    intro m a
    have h1 : (MvPolynomial.monomial m a : MvPolynomial σ k) =
        a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.coe_basisMonomials]
      simp [MvPolynomial.smul_monomial]
    rw [h1, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hP : ∀ P : MvPolynomial σ k, L P = ∑ mo ∈ P.support, P.coeff mo * w mo := by
    intro P
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hL m _
  rw [← hP]
  conv_lhs => rw [P₁.as_sum, P₂.as_sum]
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [MvPolynomial.monomial_mul, hL]
end GlobalTheory
