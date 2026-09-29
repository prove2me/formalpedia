-- Prove2me | solution 1 for ModularCurve.XOneP.flat_and_locallyOfFinitePresentation_of_isRegularLocalRing_of_isFinite_heckeRoof_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e3f50010-e314-5ec0-8b6f-d42362743a77

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
import Theorems.Thm_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_ringKrullDim_stalk_le_ringKrullDim_add_one
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_flat_and_locallyOfFinitePresentation_of_isRegularLocalRing_of_isFinite_heckeRoof_twoChartModel_x1_mul
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace G1RoofFlat

open IsLocalRing

section Loc

variable {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀] (𝔭 : Ideal A₀) [𝔭.IsPrime]

theorem free_localizedModule
    [Module.Free (Localization.AtPrime 𝔭) (Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl))] :
    Module.Free (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl B₀) := by
  set f := (IsScalarTower.toAlgHom A₀ B₀ (Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl))).toLinearMap
  haveI : IsLocalizedModule 𝔭.primeCompl f := by
    rw [isLocalizedModule_iff_isLocalization]; infer_instance
  have h1 : IsBaseChange (Localization.AtPrime 𝔭) f :=
    (isLocalizedModule_iff_isBaseChange 𝔭.primeCompl (Localization.AtPrime 𝔭) f).mp inferInstance
  have h2 : IsBaseChange (Localization.AtPrime 𝔭) (LocalizedModule.mkLinearMap 𝔭.primeCompl B₀) :=
    (isLocalizedModule_iff_isBaseChange 𝔭.primeCompl (Localization.AtPrime 𝔭) _).mp inferInstance
  exact Module.Free.of_equiv (h1.equiv.symm.trans h2.equiv)

theorem isDomain [IsDomain B₀] (hinj : Function.Injective (algebraMap A₀ B₀)) :
    IsDomain (Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)) := by
  apply IsLocalization.isDomain_localization
  rintro _ ⟨s, hs, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h => hs (by
    have : s = 0 := hinj (by rw [h, map_zero])
    rw [this]; exact 𝔭.zero_mem)

theorem le_nonZeroDivisors [IsDomain B₀] (hinj : Function.Injective (algebraMap A₀ B₀)) :
    Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl ≤ nonZeroDivisors B₀ := by
  rintro _ ⟨s, hs, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h => hs (by
    have : s = 0 := hinj (by rw [h, map_zero])
    rw [this]; exact 𝔭.zero_mem)

theorem algebraMap_injective [IsDomain A₀] [IsDomain B₀] (hinj : Function.Injective (algebraMap A₀ B₀)) :
    Function.Injective (algebraMap (Localization.AtPrime 𝔭) (Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl))) := by
  haveI : IsLocalization (Submonoid.map (algebraMap A₀ B₀) 𝔭.primeCompl)
      (Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)) := by
    show IsLocalization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl) _; infer_instance
  exact IsLocalization.map_injective_of_injective (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭)
    (Q := Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)) hinj

end Loc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem app_injective {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) (U : Y.Opens)
    (hsurj : Function.Surjective π.base) : Function.Injective (π.app U).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : π ⁻¹ᵁ (Y.basicOpen a) = ⊥ := by
    rw [Scheme.preimage_basicOpen]
    exact (AlgebraicGeometry.basicOpen_eq_bot_iff _).mpr (by simpa using ha)
  have h2 : Y.basicOpen a = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    obtain ⟨w, rfl⟩ := hsurj z
    have hw : w ∈ π ⁻¹ᵁ (Y.basicOpen a) := hz
    rw [h1] at hw
    exact hw.elim
  exact (AlgebraicGeometry.basicOpen_eq_bot_iff a).mp h2

end G1RoofFlat

open G1RoofFlat

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (π : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
    [IsFinite π.1] (hsurj : Function.Surjective π.1.base)

    (hreg : ∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j),
      IsRegularLocalRing ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x)) :
    Flat π.1 ∧ LocallyOfFinitePresentation π.1 := by
  classical

  let X : Scheme.{0} := AlgebraicCurve.TwoChartIntegralModel A (↥K) j
  let Xl : Scheme.{0} := AlgebraicCurve.TwoChartIntegralModel A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ
  let πm : Xl ⟶ X := π.1
  haveI : IsIntegral X := AlgebraicCurve.TwoChartIntegralModel.isIntegral A (↥K) j
  haveI : IsIntegral Xl := AlgebraicCurve.TwoChartIntegralModel.isIntegral A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ
  haveI : IsFinite πm := ‹IsFinite π.1›

  haveI : IsNoetherianRing A := inferInstance
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  haveI : IsProper (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) :=
    ModularCurve.isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * p)) hT
      L K hK A j hj
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
  have hsurj' : Function.Surjective πm.base := hsurj

  have key := AlgebraicGeometry.flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule πm
    (fun y => ?_)
  · exact key
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  refine ⟨U, hU, hyU, ?_⟩
  letI algAB : Algebra Γ(X, U) Γ(Xl, πm ⁻¹ᵁ U) := (πm.app U).hom.toAlgebra
  have hπU : IsAffineOpen (πm ⁻¹ᵁ U) := hU.preimage πm
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : Nonempty ↥U := ⟨⟨y, hyU⟩⟩
  obtain ⟨x, hx⟩ := hsurj' y
  haveI : Nonempty ↥(πm ⁻¹ᵁ U) := ⟨⟨x, show πm.base x ∈ U by rw [hx]; exact hyU⟩⟩
  haveI : IsDomain Γ(X, U) := @IsIntegral.component_integral _ _ U ⟨⟨y, hyU⟩⟩
  haveI : IsDomain Γ(Xl, πm ⁻¹ᵁ U) :=
    @IsIntegral.component_integral _ _ (πm ⁻¹ᵁ U) ⟨⟨x, show πm.base x ∈ U by rw [hx]; exact hyU⟩⟩
  have hinj : Function.Injective (algebraMap Γ(X, U) Γ(Xl, πm ⁻¹ᵁ U)) := app_injective πm U hsurj'
  haveI : Module.Finite Γ(X, U) Γ(Xl, πm ⁻¹ᵁ U) := IsFinite.finite_app πm U hU

  haveI : IsIntegrallyClosed Γ(Xl, πm ⁻¹ᵁ U) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) jℓ (πm ⁻¹ᵁ U) hπU

  set 𝔭 : Ideal Γ(X, U) := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal with h𝔭
  haveI : IsDomain (Localization.AtPrime 𝔭) := IsLocalization.isDomain_localization 𝔭.primeCompl_le_nonZeroDivisors
  haveI := G1RoofFlat.isDomain (A₀ := Γ(X, U)) (B₀ := Γ(Xl, πm ⁻¹ᵁ U)) 𝔭 hinj
  letI := X.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk y) 𝔭 := hU.isLocalization_stalk ⟨y, hyU⟩
  let e : X.presheaf.stalk y ≃ₐ[Γ(X, U)] Localization.AtPrime 𝔭 := IsLocalization.algEquiv 𝔭.primeCompl _ _
  haveI : IsRegularLocalRing (X.presheaf.stalk y) := hreg y
  haveI : IsRegularLocalRing (Localization.AtPrime 𝔭) := IsRegularLocalRing.of_ringEquiv e.toRingEquiv
  have hdimA : ringKrullDim (Localization.AtPrime 𝔭) ≤ 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    have h1 := AlgebraicCurve.TwoChartIntegralModel.ringKrullDim_stalk_le_ringKrullDim_add_one A (↥K) j y
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one A] at h1
    exact h1.trans (by norm_num)

  let B := Localization (Algebra.algebraMapSubmonoid Γ(Xl, πm ⁻¹ᵁ U) 𝔭.primeCompl)
  haveI : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B (Algebra.algebraMapSubmonoid Γ(Xl, πm ⁻¹ᵁ U) 𝔭.primeCompl)
      (G1RoofFlat.le_nonZeroDivisors 𝔭 hinj)
  haveI : Module.Finite (Localization.AtPrime 𝔭) B :=
    Module.Finite.of_isLocalization Γ(X, U) Γ(Xl, πm ⁻¹ᵁ U) 𝔭.primeCompl
  haveI : FaithfulSMul (Localization.AtPrime 𝔭) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (G1RoofFlat.algebraMap_injective 𝔭 hinj)
  haveI : Module.Free (Localization.AtPrime 𝔭) B :=
    Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
      (Localization.AtPrime 𝔭) hdimA B
  exact G1RoofFlat.free_localizedModule 𝔭

end S_ModularCurve_XOneP_flat_and_locallyOfFinitePresentation_of_isRegularLocalRing_of_isFinite_heckeRoof_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_flat_and_locallyOfFinitePresentation_of_isRegularLocalRing_of_isFinite_heckeRoof_twoChartModel_x1_mul (solution)
