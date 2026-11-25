-- Prove2me | solution 1 for GlobalTheory.exists_field_cm_curves_unit_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:34.893092+00:00
-- url     : https://prove2.me/submissions/0b8ebeb3-9c55-4d7b-a081-f6c96b6b7d78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Theorems.Thm_GlobalTheory_CMCurves_exists_integral_curve
import Theorems.Thm_GlobalTheory_CMCurves_isIntegral_latticeJ
import Theorems.Thm_GlobalTheory_CMCurves_finite_latticeJ
import Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
open GlobalTheory
open CMCurves
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ : K →+* ℂ),
    ¬ NumberField.ComplexEmbedding.IsReal σ →
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ a, σ a ∈ M) ∧
      ∀ L : PeriodPair, (∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) →
        ∃ W : WeierstrassCurve (𝓞 M), IsUnit W.Δ ∧
          (((W.c₄ : M) : ℂ)) ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) =
            1728 * L.g₂ ^ 3 * ((W.Δ : M) : ℂ) := by
  intro K _ _ hK σ hσ
  classical
  set S := latticeJ '' {L : PeriodPair | ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice}
  have hS : S.Finite := finite_latticeJ σ hσ
  have hcurve : ∀ j : S, ∃ E : WeierstrassCurve ℂ, IsIntegral ℤ E.a₁ ∧ IsIntegral ℤ E.a₂ ∧
      IsIntegral ℤ E.a₃ ∧ IsIntegral ℤ E.a₄ ∧ IsIntegral ℤ E.a₆ ∧ E.Δ = 1 ∧ E.c₄ ^ 3 = j := by
    rintro ⟨_, L, hL, rfl⟩
    exact exists_integral_curve (isIntegral_latticeJ hK σ L hL)
  choose E hE using hcurve
  have : Finite S := hS.to_subtype
  let T : Set ℂ := ⋃ j : S, {(E j).a₁, (E j).a₂, (E j).a₃, (E j).a₄, (E j).a₆}
  have : Finite T := (Set.finite_iUnion fun j => Set.toFinite _).to_subtype
  have hTint : ∀ z ∈ T, IsIntegral ℤ z := by
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hz
    obtain ⟨h1, h2, h3, h4, h6, -⟩ := hE j
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> assumption
  let σ' : K →ₐ[ℚ] ℂ := σ.toRatAlgHom
  have : FiniteDimensional ℚ σ'.fieldRange :=
    (AlgEquiv.ofInjectiveField σ').toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hTint z hz).tower_top
  let M : IntermediateField ℚ ℂ := σ'.fieldRange ⊔ IntermediateField.adjoin ℚ T
  have hTM : ∀ z ∈ T, z ∈ M := fun z hz =>
    (le_sup_right : IntermediateField.adjoin ℚ T ≤ M) (IntermediateField.subset_adjoin ℚ T hz)
  refine ⟨M, inferInstance, fun a => (le_sup_left : σ'.fieldRange ≤ M) ⟨a, rfl⟩, fun L hL => ?_⟩
  let j : S := ⟨latticeJ L, L, hL, rfl⟩
  obtain ⟨h1, h2, h3, h4, h6, hΔ, hc4⟩ := hE j
  have mk : ∀ z ∈ T, IsIntegral ℤ z → ∃ t : 𝓞 M, ((t : M) : ℂ) = z := fun z hz hi =>
    ⟨⟨⟨z, hTM z hz⟩, (isIntegral_algHom_iff ((M.val : M →+* ℂ).toIntAlgHom)
      Subtype.val_injective).1 hi⟩, rfl⟩
  have hmem : ∀ z ∈ ({(E j).a₁, (E j).a₂, (E j).a₃, (E j).a₄, (E j).a₆} : Set ℂ), z ∈ T :=
    fun z hz => Set.mem_iUnion.2 ⟨j, hz⟩
  obtain ⟨t1, ht1⟩ := mk _ (hmem _ (by simp)) h1
  obtain ⟨t2, ht2⟩ := mk _ (hmem _ (by simp)) h2
  obtain ⟨t3, ht3⟩ := mk _ (hmem _ (by simp)) h3
  obtain ⟨t4, ht4⟩ := mk _ (hmem _ (by simp)) h4
  obtain ⟨t6, ht6⟩ := mk _ (hmem _ (by simp)) h6
  let W : WeierstrassCurve (𝓞 M) := ⟨t1, t2, t3, t4, t6⟩
  let φ : 𝓞 M →+* ℂ := (M.val : M →+* ℂ).comp (algebraMap (𝓞 M) M)
  have hφ : Function.Injective φ :=
    Subtype.val_injective.comp RingOfIntegers.coe_injective
  have hWE : W.map φ = E j := by
    ext
    · exact ht1
    · exact ht2
    · exact ht3
    · exact ht4
    · exact ht6
  have hWΔ : W.Δ = 1 := hφ (by rw [← WeierstrassCurve.map_Δ, hWE, hΔ, map_one])
  have hWc : ((W.c₄ : M) : ℂ) = (E j).c₄ := by
    rw [← hWE, WeierstrassCurve.map_c₄]; rfl
  refine ⟨W, hWΔ ▸ isUnit_one, ?_⟩
  rw [hWc, hc4, hWΔ]
  have hd := g₂_cube_sub_g₃_sq_ne_zero L
  show latticeJ L * _ = _
  unfold latticeJ
  field_simp
  simp
end GlobalTheory
