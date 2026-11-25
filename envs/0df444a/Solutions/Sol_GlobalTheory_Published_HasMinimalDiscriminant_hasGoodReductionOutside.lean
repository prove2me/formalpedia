-- Prove2me | solution 1 for GlobalTheory.Published.HasMinimalDiscriminant.hasGoodReductionOutside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:48.019805+00:00
-- url     : https://prove2.me/submissions/86286757-8411-4352-b527-278af390e44e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
namespace GlobalTheory.Published
section Reduction
variable {F : Type} [Field F] [NumberField F]
end Reduction
section Lattice
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
variable [Algebra K ℂ]
end Lattice
section Consequences
variable {p : ℕ}
private theorem valuation_algebraMap_unit_eq_one' {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (w : Rˣ) :
    IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
      (algebraMap R K w) = 1 := by
  apply le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _)
  have h1 : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K w) *
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K ↑w⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [← h1]
  exact mul_le_of_le_one_right zero_le (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _)
variable {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F}
end Consequences
section Model
end Model
end GlobalTheory.Published
end

set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ}
namespace GlobalTheory.Published
namespace HasMinimalDiscriminant
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    {A : WeierstrassCurve F} (h : HasMinimalDiscriminant A (-(p : F) ^ 3)) :
    HasGoodReductionOutside p A := by
  intro v hv
  obtain ⟨C, u, hmin, hΔ⟩ := h v
  refine ⟨C, { toIsMinimal := hmin, goodReduction := ?_ }⟩
  have hpu : IsUnit (p : v.valuationSubringAtPrime F) := by
    have := IsLocalization.map_units (M := v.asIdeal.primeCompl) (v.valuationSubringAtPrime F)
      ⟨(p : 𝓞 F), hv⟩
    simpa using this
  obtain ⟨w, hw⟩ := u.isUnit.mul (hpu.pow 3).neg
  have hΔ' : (C • A).Δ = algebraMap (v.valuationSubringAtPrime F) F (w : v.valuationSubringAtPrime F) := by
    rw [hw, hΔ, map_mul, map_neg, map_pow, map_natCast]
    rfl
  rw [hΔ']
  exact valuation_algebraMap_unit_eq_one' w
end HasMinimalDiscriminant
end GlobalTheory.Published
