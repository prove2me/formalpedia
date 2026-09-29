-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.not_mem_range_comp_of_not_isAffinePlace_placeOfPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b30c6052-f6b8-53b2-9b0c-989c60dcd3ee

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_not_mem_range_comp_of_not_isAffinePlace_placeOfPoint
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (i : Fin 2) (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    ∀ j : Fin 2, j ≠ i → (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 ∉ Set.range (𝔛.comp A hA ρ hρ j).base := by
  intro j hji hmem
  obtain ⟨z, hz⟩ := hmem

  have ss_aff : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.IsAffinePlace p M H hpM A y := by
    rintro y ⟨x, a, hx, hv, -⟩
    exact ⟨x, a, hx, hv⟩
  have frob_aff := (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).1

  have hinv : (inv (𝔛.efib A hA ρ hρ)).base ((𝔛.efib A hA ρ hρ).base P0.1) = P0.1 := by
    show ((𝔛.efib A hA ρ hρ) ≫ inv (𝔛.efib A hA ρ hρ)).base P0.1 = P0.1
    rw [IsIso.hom_inv_id]
    rfl
  have key : ∀ (q : (𝔛.Mfib A hA ρ hρ).C) (hq : q ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C), q = P0.1 →
      (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨q, hq⟩ = (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 := by
    rintro q hq rfl
    rfl
  rw [Scheme.Hom.comp_apply] at hz
  apply hP0
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · exact absurd rfl hji
    ·
      obtain ⟨n, hn1, -⟩ := Scheme.Pullback.exists_preimage_pullback ((𝔛.efib A hA ρ hρ).base P0.1) z hz.symm
      obtain ⟨h, hpl⟩ := (𝔛.node_pin A hA ρ hρ n).2
      have hP : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (𝔛.nodeEquiv A hA ρ hρ n : _) := by
        rw [← hpl]
        exact (key _ h (by rw [hn1, hinv])).symm
      rw [hP]
      exact frob_aff _ (ss_aff _ (𝔛.nodeEquiv A hA ρ hρ n).2)
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    ·
      obtain ⟨n, -, hn2⟩ := Scheme.Pullback.exists_preimage_pullback z ((𝔛.efib A hA ρ hρ).base P0.1) hz
      obtain ⟨h, hpl⟩ := (𝔛.node_pin A hA ρ hρ n).1
      have hP : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = (𝔛.nodeEquiv A hA ρ hρ n : _) := by
        rw [← hpl]
        exact (key _ h (by rw [hn2, hinv])).symm
      rw [hP]
      exact ss_aff _ (𝔛.nodeEquiv A hA ρ hρ n).2
    · exact absurd rfl hji

#print axioms solution

end S_ModularCurve_XHDRModelAtP_not_mem_range_comp_of_not_isAffinePlace_placeOfPoint
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_not_mem_range_comp_of_not_isAffinePlace_placeOfPoint (solution)
