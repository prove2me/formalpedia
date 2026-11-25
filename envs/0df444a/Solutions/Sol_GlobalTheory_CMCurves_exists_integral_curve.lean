-- Prove2me | solution 1 for GlobalTheory.CMCurves.exists_integral_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:35.090239+00:00
-- url     : https://prove2.me/submissions/ed34096a-2476-41cf-9fec-f799c08e5572

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Theorems.Thm_GlobalTheory_exists_finite_model_ringOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
namespace GlobalTheory
namespace CMCurves
private theorem c4_pow_three_eq_j_mul_discr {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    W.c₄ ^ 3 = W.j * W.Δ := by
  rw [WeierstrassCurve.j, ← W.coe_Δ', mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
variable {K : Type} [Field K] [NumberField K]
end CMCurves
end GlobalTheory
end
end

set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
open GlobalTheory
open GlobalTheory.CMCurves
namespace GlobalTheory.CMCurves
theorem _root_.solution {j : ℂ} (hj : IsIntegral ℤ j) :
    ∃ E : WeierstrassCurve ℂ, IsIntegral ℤ E.a₁ ∧ IsIntegral ℤ E.a₂ ∧ IsIntegral ℤ E.a₃ ∧
      IsIntegral ℤ E.a₄ ∧ IsIntegral ℤ E.a₆ ∧ E.Δ = 1 ∧ E.c₄ ^ 3 = j := by
  classical
  have hjQ : IsIntegral ℚ j := hj.tower_top
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {j}
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hjQ
  have : NumberField K := ⟨⟩
  let jK : K := ⟨j, IntermediateField.mem_adjoin_simple_self ℚ j⟩
  have hWj : (WeierstrassCurve.ofJ jK).j = jK := WeierstrassCurve.ofJ_j jK
  have hjK : IsIntegral ℤ (WeierstrassCurve.ofJ jK).j := by
    rw [hWj]
    exact (isIntegral_algHom_iff ((K.val : K →+* ℂ).toIntAlgHom) Subtype.val_injective).1 hj
  obtain ⟨M, hNF, -, C, W₀, hW, hΔ⟩ := exists_finite_model_ringOfIntegers (WeierstrassCurve.ofJ jK) hjK
  have := hNF
  let ψ : M →ₐ[K] ℂ := (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] ℂ).comp M.val
  have : ((WeierstrassCurve.ofJ jK).baseChange M).IsElliptic :=
    ⟨by rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
        exact (WeierstrassCurve.isUnit_Δ _).map _⟩
  have : W₀.IsElliptic := ⟨by rw [hΔ]; exact isUnit_one⟩
  have hint : ∀ x : 𝓞 M, IsIntegral ℤ (ψ (x : M)) := fun x =>
    x.isIntegral_coe.map (ψ : M →+* ℂ).toIntAlgHom
  have h1 : (C • (WeierstrassCurve.ofJ jK).baseChange M).j = algebraMap K M jK := by
    rw [WeierstrassCurve.variableChange_j]
    erw [WeierstrassCurve.map_j, hWj]
  have h2 := c4_pow_three_eq_j_mul_discr (C • (WeierstrassCurve.ofJ jK).baseChange M)
  rw [h1, hW] at h2
  have hB : (W₀.baseChange M).Δ = 1 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, hΔ, map_one]
  refine ⟨(W₀.baseChange M).map (ψ : M →+* ℂ), hint _, hint _, hint _, hint _, hint _, ?_, ?_⟩
  · rw [WeierstrassCurve.map_Δ, hB, map_one]
  · rw [WeierstrassCurve.map_c₄, ← map_pow, h2, hB, mul_one]
    show ψ (algebraMap K M jK) = j
    rw [AlgHom.commutes]
    rfl
end GlobalTheory.CMCurves
