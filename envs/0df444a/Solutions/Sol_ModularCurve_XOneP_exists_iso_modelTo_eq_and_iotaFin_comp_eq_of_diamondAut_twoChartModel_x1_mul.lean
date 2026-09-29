-- Prove2me | solution 1 for ModularCurve.XOneP.exists_iso_modelTo_eq_and_iotaFin_comp_eq_of_diamondAut_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a2d48eae-6115-53c0-a56c-85959303bc61

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv
import Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
import Theorems.Thm_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut
import Theorems.Thm_ModularCurve_isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_iso_modelTo_eq_and_iotaFin_comp_eq_of_diamondAut_twoChartModel_x1_mul
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WexBody

open scoped MatrixGroups

theorem isSeparated_toBase_congr (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F]
    {j j' : F} [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (h : j = j')
    [IsSeparated (AlgebraicCurve.TwoChartIntegralModel.toBase R F j')] :
    IsSeparated (AlgebraicCurve.TwoChartIntegralModel.toBase R F j) := by
  subst h; assumption

theorem finiteType_chartAlgInf_congr (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F]
    {j j' : F} (h : j = j')
    [Algebra.FiniteType R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j')] :
    Algebra.FiniteType R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j) := by
  subst h; assumption

theorem jq_mem (Γ : Subgroup SL(2, ℤ)) : ModularCurve.jq ∈ ModularCurve.qExpFunctionFieldC ℚ Γ := by
  have h := ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ
  rw [ModularCurve.jqModC_rat] at h
  exact ModularCurve.intFormRatiosC_subset ℚ Γ h

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve in

theorem baseChangeAut_refl_apply (L : Type*) [Field L] [Algebra ℚ L]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (z : ↥(laurentBaseChange L F₀)) :
    baseChangeAut L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) z = z := by
  rcases Classical.em (∃ σ : ↥(laurentBaseChange L F₀) ≃ₐ[L] ↥(laurentBaseChange L F₀),
      IsBaseChangeAutOf L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) σ) with hex | hex
  · have hσ := isBaseChangeAutOf_baseChangeAut hex
    set σ := baseChangeAut L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) with hσdef
    obtain ⟨z, hz⟩ := z
    apply Subtype.ext
    show ((σ ⟨z, hz⟩ : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = z
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact hσ ⟨y, hy⟩
    | algebraMap a =>
      have : (⟨algebraMap L (LaurentSeries L) a, IntermediateField.algebraMap_mem _ a⟩ : ↥(laurentBaseChange L F₀)) =
          algebraMap L ↥(laurentBaseChange L F₀) a := rfl
      rw [this, AlgEquiv.commutes]
      rfl
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, IntermediateField.add_mem _ hx hy⟩ : ↥(laurentBaseChange L F₀)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, IntermediateField.coe_add, ihx, ihy]
    | inv x hx ihx =>
      have : (⟨x⁻¹, IntermediateField.inv_mem _ hx⟩ : ↥(laurentBaseChange L F₀)) = (⟨x, hx⟩ : ↥(laurentBaseChange L F₀))⁻¹ := rfl
      rw [this, map_inv₀, IntermediateField.coe_inv, ihx]
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, IntermediateField.mul_mem _ hx hy⟩ : ↥(laurentBaseChange L F₀)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, IntermediateField.coe_mul, ihx, ihy]
  · rw [baseChangeAut_of_not hex]
    rfl

end WexBody

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

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
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p))

    (d : ℕ) (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) :
    ∃ (w : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
      (ρ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
      w.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j ∧
      w.inv ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j ∧
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((ρ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = θ b) ∧
      ModularCurve.TwoChart.ιFin A (↥K) j ≫ w.hom = Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
  classical
  subst hK

  have hθeq : ∀ x, θ x = ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x :=
    fun x => Subtype.ext (hθ x x rfl)

  have hθj : θ j = j := by
    by_cases hd : d.Coprime (M * p)
    · exact ModularCurve.algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_qExpFunctionFieldC_gamma0_of_coe_eq_baseChangeAut_diamondAut
        (M * p) L _ rfl d hd θ hθ j
        (by rw [hj]; exact ModularCurve.coeffEmb_mem_laurentBaseChange L (WexBody.jq_mem (CongruenceSubgroup.Gamma0 (M * p))))
    · rw [hθeq, ModularCurve.diamondAut_of_not_coprime hd]
      exact WexBody.baseChangeAut_refl_apply L j

  have hθA : ∀ a : A, θ (algebraMap A _ a) = algebraMap A _ a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L, AlgEquiv.commutes]
  let σ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) ≃ₐ[A]
      ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    { θ.toRingEquiv with commutes' := hθA }
  have hσ : ∀ x, σ x = θ x := fun _ => rfl
  have hσj : σ j = j := hθj

  haveI : Fact (σ j ≠ 0) := ⟨by rw [hσj]; exact Fact.out⟩
  haveI hP : IsProper (AlgebraicCurve.TwoChartIntegralModel.toBase A
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) j) :=
    ModularCurve.isProper_toBase_twoChartIntegralModel_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * p))
      (WexBody.T_mem_Gamma1 _) L (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) rfl A j hj

  haveI hFT : Algebra.FiniteType A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A
      (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) j) := by
    have h1 : LocallyOfFiniteType (AlgebraicCurve.TwoChartIntegralModel.ιInf A
        (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) j ≫
        AlgebraicCurve.TwoChartIntegralModel.toBase A _ j) := inferInstance
    rw [AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase] at h1
    exact RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h1)
  haveI : IsSeparated (AlgebraicCurve.TwoChartIntegralModel.toBase A _ (σ j)) := WexBody.isSeparated_toBase_congr A _ hσj
  haveI : Algebra.FiniteType A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ (σ j)) :=
    WexBody.finiteType_chartAlgInf_congr A _ hσj
  have hjmem : j ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A _ j :=
    (AlgebraicCurve.TwoChartIntegralModel.jChartFin A _ j).2
  have hfin : σ j ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A _ j := by rw [hσj]; exact hjmem
  have hfin' : j ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A _ (σ j) := by rw [hσj]; exact hjmem
  have hvis : ∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ (σ j),
      ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ j,
        (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ j, s = 1 + j⁻¹ * a) ∧
          s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ j := by
    intro y hy
    rw [hσj] at hy
    refine ⟨1, one_mem _, ⟨0, zero_mem _, ?_⟩, ?_⟩
    · rw [mul_zero, add_zero]
    · rw [one_mul]; exact hy
  have hvis' : ∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ j,
      ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ (σ j),
        (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ (σ j), s = 1 + (σ j)⁻¹ * a) ∧
          s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A _ (σ j) := by
    intro y hy
    rw [hσj]
    refine ⟨1, one_mem _, ⟨0, zero_mem _, ?_⟩, ?_⟩
    · rw [mul_zero, add_zero]
    · rw [one_mul]; exact hy

  obtain ⟨w₀, θc, hw₀, hθc, hsq₀, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_toBase_eq_and_iotaFin_comp_eq_of_algEquiv A _ j σ hfin hfin' hvis hvis'

  obtain ⟨e, he, heFin, -⟩ := ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo A
    (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) j
  have heinv : e.inv ≫ ModularCurve.TwoChart.modelTo A _ j = AlgebraicCurve.TwoChartIntegralModel.toBase A _ j := by
    rw [← he, e.inv_hom_id_assoc]
  let w : ModularCurve.TwoChartModel A _ j ≅ ModularCurve.TwoChartModel A _ j := e ≪≫ w₀ ≪≫ e.symm
  have hw : w.hom ≫ ModularCurve.TwoChart.modelTo A _ j = ModularCurve.TwoChart.modelTo A _ j := by
    show (e.hom ≫ w₀.hom ≫ e.inv) ≫ _ = _
    rw [Category.assoc, Category.assoc, heinv, hw₀, he]
  have hw₀inv : w₀.inv ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A _ j =
      AlgebraicCurve.TwoChartIntegralModel.toBase A _ j := by
    rw [Iso.inv_comp_eq]
    exact hw₀.symm
  have hw' : w.inv ≫ ModularCurve.TwoChart.modelTo A _ j = ModularCurve.TwoChart.modelTo A _ j := by
    show (e.hom ≫ w₀.inv ≫ e.inv) ≫ _ = _
    rw [Category.assoc, Category.assoc, heinv, hw₀inv, he]
  refine ⟨w, θc.toRingEquiv, hw, hw', fun b => hθc b, ?_⟩

  have hιFin : ModularCurve.TwoChart.ιFin A _ j = AlgebraicCurve.TwoChartIntegralModel.ιFin A _ j ≫ e.inv :=
    (Iso.eq_comp_inv e).mpr heFin
  show ModularCurve.TwoChart.ιFin A _ j ≫ (e.hom ≫ w₀.hom ≫ e.inv) =
    Spec.map (CommRingCat.ofHom θc.toRingEquiv.toRingHom) ≫ ModularCurve.TwoChart.ιFin A _ j
  have key : AlgebraicCurve.TwoChartIntegralModel.ιFin A _ j ≫ e.inv ≫ e.hom ≫ w₀.hom ≫ e.inv =
      Spec.map (CommRingCat.ofHom θc.toRingEquiv.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin A _ j ≫ e.inv := by
    rw [e.inv_hom_id_assoc, reassoc_of% hsq₀]
  rw [hιFin]
  exact key

end S_ModularCurve_XOneP_exists_iso_modelTo_eq_and_iotaFin_comp_eq_of_diamondAut_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_iso_modelTo_eq_and_iotaFin_comp_eq_of_diamondAut_twoChartModel_x1_mul (solution)
