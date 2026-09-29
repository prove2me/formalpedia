-- Prove2me | solution 1 for ModularCurve.TwoChart.exists_hom_modelTo_comp_eq_and_iotaFin_comp_eq_of_le_laurentBaseChange_x1FunctionField_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9eb29dcd-f9f7-5b7a-a7ea-087d15dc7058

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_isFinite_surjective_chartMap_finite_of_algHom
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TwoChart_exists_hom_modelTo_comp_eq_and_iotaFin_comp_eq_of_le_laurentBaseChange_x1FunctionField_mul
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ForgetMap

open AlgebraicCurve.TwoChartIntegralModel

def restrictA (A : Type) {L : Type} [CommRing A] [Field L] [Algebra A L] {E E' : Type} [Field E] [Field E']
    [Algebra L E] [Algebra L E'] [Algebra A E] [Algebra A E'] [IsScalarTower A L E] [IsScalarTower A L E']
    (f : E →ₐ[L] E') : E →ₐ[A] E' :=
  { f.toRingHom with
    commutes' := fun a => by
      change f (algebraMap A E a) = algebraMap A E' a
      rw [IsScalarTower.algebraMap_apply A L E, IsScalarTower.algebraMap_apply A L E', AlgHom.commutes] }

theorem restrictA_apply {A L : Type} [CommRing A] [Field L] [Algebra A L] {E E' : Type} [Field E] [Field E']
    [Algebra L E] [Algebra L E'] [Algebra A E] [Algebra A E'] [IsScalarTower A L E] [IsScalarTower A L E']
    (f : E →ₐ[L] E') (x : E) : restrictA A f x = f x := rfl

theorem chartData
    (N : ℕ) [NeZero N] (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (F : IntermediateField L (LaurentSeries L)) (hF : F = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    [Algebra A ↥F] [IsScalarTower A L ↥F]
    (x : ↥F) (hx : ((x : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (x ≠ 0)] :
    FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥F)) ↥F ∧
    (IsNoetherianRing ↥(chartAlgFin A (↥F) x) ∧ IsFractionRing ↥(chartAlgFin A (↥F) x) ↥F) ∧
    (IsNoetherianRing ↥(chartAlgInf A (↥F) x) ∧ IsFractionRing ↥(chartAlgInf A (↥F) x) ↥F) := by
  have htx : Transcendental A x := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L F A x hx
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥F)) ↥F :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 N) (by simp [ModularGroup.T]) L F hF x hx
  haveI := hFD
  haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({x} : Set ↥F)) ↥F := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({x} : Set ↥F)) ↥F := inferInstance
  obtain ⟨hFT0, hFT0'⟩ := finiteType_chartAlgFin_and_chartAlgInf A L (↥F) x htx hFD hsep
  haveI := hFT0; haveI := hFT0'
  have hadj : IntermediateField.adjoin L ({x⁻¹} : Set ↥F) = IntermediateField.adjoin L ({x} : Set ↥F) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self L x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self L x⁻¹)
      rwa [inv_inv] at h
  haveI hAlg' : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({x⁻¹} : Set ↥F)) ↥F := by rw [hadj]; exact hAlg
  exact ⟨hFD, ⟨Algebra.FiniteType.isNoetherianRing A _, isFractionRing_chartAlg A L (↥F) {x}⟩,
    ⟨Algebra.FiniteType.isNoetherianRing A _, isFractionRing_chartAlg A L (↥F) {x⁻¹}⟩⟩

end ForgetMap

open ForgetMap AlgebraicCurve.TwoChartIntegralModel in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
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

    (KM : IntermediateField L (LaurentSeries L))
    (hKM : KM = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥KM] [IsScalarTower A L ↥KM]
    (jM : ↥KM) (hjM : ((jM : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jM ≠ 0)]
    (hle : KM ≤ K) :
    ∃ (f : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥KM) jM)
      (ιF : ↥(ModularCurve.TwoChart.chartAlgFin A (↥KM) jM) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
      (ιI : ↥(ModularCurve.TwoChart.chartAlgInf A (↥KM) jM) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)),

      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥KM) jM), (((ιF b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) = ((b : ↥KM) : LaurentSeries L)) ∧
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥KM) jM), (((ιI b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : ↥K) : LaurentSeries L) = ((b : ↥KM) : LaurentSeries L)) ∧

      f ≫ ModularCurve.TwoChart.modelTo A (↥KM) jM = ModularCurve.TwoChart.modelTo A (↥K) j ∧

      ModularCurve.TwoChart.ιFin A (↥K) j ≫ f = Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥KM) jM ∧
      ModularCurve.TwoChart.ιInf A (↥K) j ≫ f = Spec.map (CommRingCat.ofHom ιI.toRingHom) ≫ ModularCurve.TwoChart.ιInf A (↥KM) jM ∧

      f ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥KM) jM).opensRange = (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange ∧
      f ⁻¹ᵁ (ModularCurve.TwoChart.ιInf A (↥KM) jM).opensRange = (ModularCurve.TwoChart.ιInf A (↥K) j).opensRange ∧

      IsFinite f ∧ Function.Surjective f.base := by
  classical

  let φ : ↥KM →ₐ[A] ↥K := restrictA A (IntermediateField.inclusion hle)
  have hφcoe : ∀ y : ↥KM, ((φ y : ↥K) : LaurentSeries L) = ((y : ↥KM) : LaurentSeries L) := fun y => rfl
  have hφj : φ jM = j := Subtype.ext (by rw [hφcoe, hjM, hj])

  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨hFDM, hFfin, hFinf⟩ := chartData M L A KM hKM jM hjM
  obtain ⟨hFD, -, -⟩ := chartData (M * p) L A K hK j hj

  have hφfin : φ.toRingHom.Finite := by
    letI : Algebra ↥KM ↥K := φ.toRingHom.toAlgebra
    have hsub : (IntermediateField.adjoin L ({j} : Set ↥K)).toSubalgebra.toSubring ≤ φ.toRingHom.range := by
      intro y hy
      have : IntermediateField.adjoin L ({j} : Set ↥K) ≤ (IntermediateField.inclusion hle).fieldRange := by
        rw [IntermediateField.adjoin_simple_le_iff]
        exact ⟨jM, by rw [← hφj]; rfl⟩
      obtain ⟨z, hz⟩ := this hy
      exact ⟨z, hz⟩

    obtain ⟨s, hs⟩ := Module.finite_def.mp hFD
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span ↥(IntermediateField.adjoin L ({j} : Set ↥K)) (s : Set ↥K) := by rw [hs]; trivial
    refine Submodule.span_induction (fun z hz => Submodule.subset_span hz) (Submodule.zero_mem _)
      (fun _ _ _ _ ha hb => Submodule.add_mem _ ha hb) (fun c z _ hz => ?_) hy
    obtain ⟨c', hc'⟩ := hsub c.2
    have : (c • z : ↥K) = c' • z := by
      change (c : ↥K) * z = φ.toRingHom c' * z
      rw [hc']
    rw [this]
    exact Submodule.smul_mem _ c' hz

  obtain ⟨m, ιF, ιI, hιF, hιI, hmb, hsqF, hsqI, hpreF, hpreI, hfin, hsurj, -, -, -, -⟩ :=
    exists_hom_isFinite_surjective_chartMap_finite_of_algHom A ↥KM ↥K φ hφfin jM j hφj hFfin hFinf
  exact ⟨m, ιF, ιI, fun b => (congrArg (fun z : ↥K => (z : LaurentSeries L)) (hιF b)).trans (hφcoe b),
    fun b => (congrArg (fun z : ↥K => (z : LaurentSeries L)) (hιI b)).trans (hφcoe b), hmb, hsqF.symm, hsqI.symm, hpreF, hpreI,
    hfin, hsurj⟩

end S_ModularCurve_TwoChart_exists_hom_modelTo_comp_eq_and_iotaFin_comp_eq_of_le_laurentBaseChange_x1FunctionField_mul
end P2MW
export P2MW.S_ModularCurve_TwoChart_exists_hom_modelTo_comp_eq_and_iotaFin_comp_eq_of_le_laurentBaseChange_x1FunctionField_mul (solution)
