-- Prove2me | solution 1 for ModularCurve.XOneP.smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e57405f3-35b4-5bde-9532-f0aa6fb3fa86

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
import Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "TwoChart.modelTo x1FunctionField jq coeffEmb laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo"
namespace XOneP
namespace GenFacts
p2m_open "ModularCurve"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem transfer_pullback_snd (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S) (e : X ≅ X') (he : e.hom ≫ f' = f) (g : T ⟶ S)
    (h : P (pullback.snd f' g)) : P (pullback.snd f g) := by
  have sq : IsPullback (pullback.fst f' g) (pullback.snd f' g) f' g := IsPullback.of_hasPullback f' g
  have t : IsPullback e.inv f' f (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [← he, Iso.inv_hom_id_assoc, Category.comp_id]⟩
  have hp : IsPullback (pullback.fst f' g ≫ e.inv) (pullback.snd f' g) f g := by
    simpa using sq.paste_horiz t
  rw [← hp.isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr h

end ModularCurve.XOneP.GenFacts

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) ∧
    GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) := by

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  haveI := hFD
  haveI : CharZero ↥(IntermediateField.adjoin L ({j} : Set ↥K)) :=
    charZero_of_injective_algebraMap (algebraMap L ↥(IntermediateField.adjoin L ({j} : Set ↥K))).injective
  haveI : PerfectField ↥(IntermediateField.adjoin L ({j} : Set ↥K)) := PerfectField.ofCharZero
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  have h80 := AlgebraicCurve.TwoChartIntegralModel.smoothOfRelativeDimension_one_pullback_snd_toBase_of_charZero
    A L (↥K) j htj hFD hsep L
  obtain ⟨e, he, -, -⟩ := ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo A (↥K) j
  have hiso : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨?_, ?_⟩
  · exact ModularCurve.XOneP.GenFacts.transfer_pullback_snd (@SmoothOfRelativeDimension.{0} 1) _ _ e he _ h80
  ·
    have hgi :=
      AlgebraicCurve.TwoChartIntegralModel.geometricallyIntegral_baseChange_toBase_of_intermediateField_laurentSeries L K A j
    exact ModularCurve.XOneP.GenFacts.transfer_pullback_snd (@GeometricallyIntegral.{0}) _ _ e he _ hgi

end S_ModularCurve_XOneP_smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_smoothOfRelativeDimension_one_and_geometricallyIntegral_baseChange_twoChartModel_x1_mul (solution)
