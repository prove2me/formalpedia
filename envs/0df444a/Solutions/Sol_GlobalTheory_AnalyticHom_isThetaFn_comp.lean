-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.isThetaFn_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:48.733562+00:00
-- url     : https://prove2.me/submissions/5241cc79-ffc8-44c0-9d1e-252d7f1a033a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g')
namespace GlobalTheory.AnalyticHom
theorem _root_.solution {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ} (hχ : ∀ l, χ l ^ 2 = 1)
    (hχ' : ∀ l, χ' l ^ 2 = 1) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (n : ℕ)
    (hΛ : ∀ l ∈ u.Λ, F l ∈ u'.Λ)
    (hH : ∀ z w, hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w) {N : ℕ}
    {θ₁ θ₂ : (Fin g' → ℂ) → ℂ} (h₁ : u'.IsThetaFn Hm' χ' N θ₁) (h₂ : u'.IsThetaFn Hm' χ' N θ₂) :
    u.IsThetaFn Hm χ (2 * (n * N)) fun z => θ₁ (F z) * θ₂ (F z) := by
  have hF : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
  refine ⟨(h₁.1.comp hF).mul (h₂.1.comp hF), fun l z => ?_⟩
  have k₁ := h₁.2 ⟨F l, hΛ l l.2⟩ (F z)
  have k₂ := h₂.2 ⟨F l, hΛ l l.2⟩ (F z)
  simp only [hH] at k₁ k₂
  have e : Complex.exp (Real.pi * (n * hermForm Hm z l) + Real.pi / 2 * (n * hermForm Hm l l)) =
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [map_add]
  rw [k₁, k₂, e]
  generalize Complex.exp _ = E
  have a₁ : χ l ^ (2 * (n * N)) = 1 := by rw [pow_mul, hχ, one_pow]
  have a₂ : χ' ⟨F l, hΛ l l.2⟩ ^ (2 * N) = 1 := by rw [pow_mul, hχ', one_pow]
  rw [mul_pow (χ l), a₁]
  linear_combination (E ^ (2 * (n * N)) * θ₁ (F z) * θ₂ (F z)) * a₂
end GlobalTheory.AnalyticHom
