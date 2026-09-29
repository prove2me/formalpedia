-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fcabc315-ca09-538f-b570-e883388f202c

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP coeffMap coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb jqModC xHFunctionFieldBar qExpFunctionFieldC XHDRModelAtP exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta_chart_nonempty w Meta efib hefib comp_over Meta_pin Mfib comp isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd"
namespace GaussStalkCore
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

noncomputable def reader {X G : Scheme.{0}} [IsIntegral G] (g : G ⟶ X) {T : Type} [CommRing T]
    (e : G.functionField →+* T) (O : X.Opens) [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O))] : Γ(X, O) →+* T :=
  e.comp ((G.germToFunctionField (g ⁻¹ᵁ O)).hom.comp (g.app O).hom)

theorem reader_apply {X G : Scheme.{0}} [IsIntegral G] (g : G ⟶ X) {T : Type} [CommRing T]
    (e : G.functionField →+* T) (O : X.Opens) [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O))] (s : Γ(X, O)) :
    reader g e O s = e (G.germToFunctionField (g ⁻¹ᵁ O) ((g.app O).hom s)) := rfl

theorem reader_res {X G : Scheme.{0}} [IsIntegral G] (g : G ⟶ X) {T : Type} [CommRing T]
    (e : G.functionField →+* T) (O O' : X.Opens) (h : O' ≤ O)
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O))] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ O'))] (s : Γ(X, O)) :
    reader g e O' ((X.presheaf.map (homOfLE h).op).hom s) = reader g e O s := by
  simp only [reader_apply]
  congr 1
  have h1 : (g.app O').hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (G.presheaf.map (homOfLE (show g ⁻¹ᵁ O' ≤ g ⁻¹ᵁ O from fun x hx => h hx)).op).hom ((g.app O).hom s) := by
    have h2 := congrArg (fun φ => φ.hom s) (g.naturality (homOfLE h).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    exact h2
  rw [h1]
  exact TopCat.Presheaf.germ_res_apply G.presheaf _ _ _ _

theorem exists_witness {XP MC MF : Scheme.{0}} [IsIntegral MC] [IsIntegral MF] (gA : MC ⟶ XP) (t : MF ⟶ XP)
    {TB Tκ Λ : Type} [CommRing TB] [CommRing Tκ] [Nontrivial Tκ] [CommRing Λ]
    (eB : MC.functionField →+* TB) (eκ : MF.functionField →+* Tκ) (ιB : Λ →+* TB) (ικ : Λ →+* Tκ)
    (U V W : XP.Opens) (hWU : W ≤ U) (hWV : W ≤ V)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ V))]
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W))]
    [Nonempty (Scheme.Opens.toScheme (t ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme (t ⁻¹ᵁ V))]
    [Nonempty (Scheme.Opens.toScheme (t ⁻¹ᵁ W))]
    (S : Set Γ(XP, V))
    (hS : ∀ x ∈ S, ∃ w : Λ, eB (MC.germToFunctionField (gA ⁻¹ᵁ V) ((gA.app V).hom x)) = ιB w ∧
        eκ (MF.germToFunctionField (t ⁻¹ᵁ V) ((t.app V).hom x)) = ικ w)
    (σ τ : Γ(XP, V)) (hσ : σ ∈ Subring.closure S) (hτ : τ ∈ Subring.closure S)
    (hunit : IsUnit ((XP.presheaf.map (homOfLE hWV).op).hom τ))
    (s : Γ(XP, U))
    (heq : (XP.presheaf.map (homOfLE hWU).op).hom s * (XP.presheaf.map (homOfLE hWV).op).hom τ =
        (XP.presheaf.map (homOfLE hWV).op).hom σ) :
    ∃ xs ys : Λ, ικ ys ≠ 0 ∧
      eB (MC.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) * ιB ys = ιB xs ∧
      eκ (MF.germToFunctionField (t ⁻¹ᵁ U) ((t.app U).hom s)) * ικ ys = ικ xs := by

  have hP : ∀ x ∈ Subring.closure S, ∃ w : Λ, reader gA eB V x = ιB w ∧ reader t eκ V x = ικ w := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx => exact hS x hx
    | zero => exact ⟨0, by simp⟩
    | one => exact ⟨1, by simp⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨a, ha, ha'⟩ := ihx
        obtain ⟨b, hb, hb'⟩ := ihy
        exact ⟨a + b, by rw [map_add, ha, hb, map_add], by rw [map_add, ha', hb', map_add]⟩
    | neg x _ ihx =>
        obtain ⟨a, ha, ha'⟩ := ihx
        exact ⟨-a, by rw [map_neg, ha, map_neg], by rw [map_neg, ha', map_neg]⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨a, ha, ha'⟩ := ihx
        obtain ⟨b, hb, hb'⟩ := ihy
        exact ⟨a * b, by rw [map_mul, ha, hb, map_mul], by rw [map_mul, ha', hb', map_mul]⟩
  obtain ⟨xs, hxs, hxs'⟩ := hP σ hσ
  obtain ⟨ys, hys, hys'⟩ := hP τ hτ
  refine ⟨xs, ys, ?_, ?_, ?_⟩
  ·
    have hu : IsUnit (reader t eκ W ((XP.presheaf.map (homOfLE hWV).op).hom τ)) := hunit.map _
    rw [reader_res t eκ V W hWV, hys'] at hu
    exact hu.ne_zero
  · have h := congrArg (reader gA eB W) heq
    rw [map_mul, reader_res gA eB U W hWU, reader_res gA eB V W hWV, reader_res gA eB V W hWV, hxs, hys] at h
    exact h
  · have h := congrArg (reader t eκ W) heq
    rw [map_mul, reader_res t eκ U W hWU, reader_res t eκ V W hWV, reader_res t eκ V W hWV, hxs', hys'] at h
    exact h

end ModularCurve.XHDRModelAtP.GaussStalkCore

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP coeffMap coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb jqModC xHFunctionFieldBar qExpFunctionFieldC XHDRModelAtP exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta_chart_nonempty w Meta efib hefib comp_over Meta_pin Mfib comp isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd"
namespace GaussStalk
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

theorem germToFunctionField_app_app_of_comp_eq {M X Y : Scheme.{0}} [IrreducibleSpace M]
    (t : M ⟶ X) (F : X ⟶ Y) (φ : M ⟶ Y) (h : t ≫ F = φ) (O : Y.Opens)
    [Nonempty (Scheme.Opens.toScheme (t ⁻¹ᵁ (F ⁻¹ᵁ O)))] [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ O))]
    (x : Γ(Y, O)) :
    M.germToFunctionField (t ⁻¹ᵁ (F ⁻¹ᵁ O)) ((t.app (F ⁻¹ᵁ O)).hom ((F.app O).hom x)) =
      M.germToFunctionField (φ ⁻¹ᵁ O) ((φ.app O).hom x) := by
  subst h
  rfl

end ModularCurve.XHDRModelAtP.GaussStalk

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ord_inv TwoChartIntegralModel TwoChartIntegralModel.ιFin_toBase TwoChartIntegralModel.ιInf_toBase TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf baseToFunctionField CurveModel CurveModel.range_stalk_eq" namespace CurveModel p2m_export "AlgebraicCurve.CurveModel" "placeOfPoint toBase C range_stalk_eq ffEquiv ffEquiv_algebraMap smooth" end AlgebraicCurve.CurveModel
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.CurveModel" in

theorem AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] (Mc : AlgebraicCurve.CurveModel K L)
    (U : Mc.C.Opens) (P : closedPoints Mc.C) (hP : P.1 ∈ U)
    [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(Mc.C, U)) (hs : IsUnit s) :
    (Mc.placeOfPoint P).ord (Mc.ffEquiv.symm (Mc.C.germToFunctionField U s)) = 0 := by

  let φ : Mc.C.presheaf.stalk P.1 →+* L :=
    (Mc.ffEquiv.symm : Mc.C.functionField ≃+* L).toRingHom.comp (algebraMap (Mc.C.presheaf.stalk P.1) Mc.C.functionField)
  have hrange : φ.range = (Mc.placeOfPoint P).toValuationSubring.toSubring := Mc.range_stalk_eq P

  let g : Mc.C.presheaf.stalk P.1 := Mc.C.presheaf.germ U P.1 hP s
  have hg : IsUnit g := hs.map _
  have hgerm : Mc.C.germToFunctionField U s = algebraMap (Mc.C.presheaf.stalk P.1) Mc.C.functionField g := by
    change algebraMap Γ(Mc.C, U) Mc.C.functionField s = _
    exact IsScalarTower.algebraMap_apply Γ(Mc.C, U) (Mc.C.presheaf.stalk ((⟨P.1, hP⟩ : U) : Mc.C)) Mc.C.functionField s
  have hx : Mc.ffEquiv.symm (Mc.C.germToFunctionField U s) = φ g := by
    rw [hgerm]
    rfl
  rw [hx]

  have hmem : ∀ t : Mc.C.presheaf.stalk P.1, φ t ∈ (Mc.placeOfPoint P).toValuationSubring := fun t => by
    have ht : φ t ∈ φ.range := ⟨t, rfl⟩
    rw [hrange] at ht
    exact ht
  have hinv : φ g * φ ((hg.unit⁻¹ : (Mc.C.presheaf.stalk P.1)ˣ) : Mc.C.presheaf.stalk P.1) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have hne : φ g ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hinv
    exact zero_ne_one hinv
  have h1 : 0 ≤ (Mc.placeOfPoint P).ord (φ g) :=
    ((Mc.placeOfPoint P).mem_iff_ord_nonneg hne).mp (hmem g)
  have hinv' : (φ g)⁻¹ = φ ((hg.unit⁻¹ : (Mc.C.presheaf.stalk P.1)ˣ) : Mc.C.presheaf.stalk P.1) :=
    (eq_inv_of_mul_eq_one_right hinv).symm ▸ rfl
  have h2 : 0 ≤ (Mc.placeOfPoint P).ord (φ g)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hinv]
    exact ((Mc.placeOfPoint P).mem_iff_ord_nonneg (fun h0 => by
      rw [← inv_eq_of_mul_eq_one_right hinv] at h0
      exact (inv_ne_zero hne) h0)).mp (hmem _)
  rw [AlgebraicCurve.Place.ord_inv] at h2
  omega

namespace ModularCurve p2m_export "ModularCurve" "JZeroNeronObjectAtP coeffMap coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb jqModC xHFunctionFieldBar qExpFunctionFieldC XHDRModelAtP exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd" namespace XHDRModelAtP p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta_chart_nonempty w Meta efib hefib comp_over Meta_pin Mfib comp isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd" end ModularCurve.XHDRModelAtP
p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve in

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_fst_iotaFin_eq_coeffEmb
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))))]
    (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))
        ((gA.app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
  haveI := 𝔛.Meta_chart_nonempty
  refine Eq.trans ?_ (𝔛.Meta_pin b)
  exact congrArg (fun z => ((𝔛.Meta.ffEquiv.symm z : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))
    (ModularCurve.XHDRModelAtP.GaussStalk.germToFunctionField_app_app_of_comp_eq gA (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) _ hgA₁ _ _)

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve in

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_fst_iotaInf_eq_coeffEmb
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))))]
    (b : ↥(chartAlgInf p (ΓM M H) hj)) :
    ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))
        ((gA.app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b))))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
  obtain ⟨hne, hread⟩ :=
    ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb p M H hpM hj 𝔛 b
  haveI := hne
  refine Eq.trans ?_ hread
  exact congrArg (fun z => ((𝔛.Meta.ffEquiv.symm z : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))
    (ModularCurve.XHDRModelAtP.GaussStalk.germToFunctionField_app_app_of_comp_eq gA (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) _ hgA₁ _ _)

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve in

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_comp_bc_app_fst_iotaFin_eq_coeffMap
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    [Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))))]
    (b : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) :
    ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))
        (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b)))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      coeffMap ((IsLocalRing.residue ↥Pl).comp ρ) y := by
  obtain ⟨hne, hread⟩ :=
    ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
      p M H hpM hpM2 hHp hj 𝔛 Pl hPl ρ hρ b
  haveI := hne
  have hTF : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) =
      𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))) := by
    simp only [Category.assoc, hbc₁]
  refine Eq.trans ?_ (hread y hy)
  exact congrArg (fun z => (((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm z : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)))
    (ModularCurve.XHDRModelAtP.GaussStalk.germToFunctionField_app_app_of_comp_eq (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) _ hTF _ _)

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve in

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_comp_bc_app_fst_iotaInf_eq_coeffMap
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    [Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))))]
    (b : ↥(chartAlgInf p (ΓM M H) hj)) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) :
    ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))
        (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b)))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      coeffMap ((IsLocalRing.residue ↥Pl).comp ρ) y := by
  obtain ⟨hne, hread⟩ :=
    ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd
      p M H hpM hpM2 hHp hj 𝔛 Pl hPl ρ hρ b
  haveI := hne
  have hTF : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) =
      𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ))) := by
    simp only [Category.assoc, hbc₁]
  refine Eq.trans ?_ (hread y hy)
  exact congrArg (fun z => (((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm z : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)))
    (ModularCurve.XHDRModelAtP.GaussStalk.germToFunctionField_app_app_of_comp_eq (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) _ hTF _ _)

namespace ScalarReadAux

theorem germ_top_appTop_congr {Y X : Scheme.{0}} [IsIntegral Y] {φ ψ : Y ⟶ X} (h : φ = ψ) (x : Γ(X, ⊤)) :
    (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (φ.appTop.hom x) =
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (ψ.appTop.hom x) := by
  subst h
  rfl

theorem germToFunctionField_preimage_top_eq {Y X : Scheme.{0}} [IsIntegral Y] (φ : Y ⟶ X)
    [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ⊤))] (x : Γ(X, ⊤)) :
    Y.germToFunctionField (φ ⁻¹ᵁ ⊤) ((φ.app ⊤).hom x) = (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (φ.appTop.hom x) := by
  rfl

theorem germToFunctionField_app_appTop_eq_germ_comp_appTop {Y X Z : Scheme.{0}} [IsIntegral Y] (φ : Y ⟶ X) (χ : X ⟶ Z)
    [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ⊤))] (x : Γ(Z, ⊤)) :
    Y.germToFunctionField (φ ⁻¹ᵁ ⊤) ((φ.app ⊤).hom (χ.appTop.hom x)) =
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom ((φ ≫ χ).appTop.hom x) := by
  rfl

theorem germToFunctionField_app_appTop_eq_of_comp_eq {Y X S : Scheme.{0}} [IsIntegral Y] (φ : Y ⟶ X) (snd : X ⟶ S) (ψ : Y ⟶ S)
    (hc : φ ≫ snd = ψ) [Nonempty (Scheme.Opens.toScheme (φ ⁻¹ᵁ ⊤))] (x : Γ(S, ⊤)) :
    Y.germToFunctionField (φ ⁻¹ᵁ ⊤) ((φ.app ⊤).hom (snd.appTop.hom x)) =
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom (ψ.appTop.hom x) := by
  subst hc
  rfl

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := by
  rfl

theorem appTop_specMap_ΓSpecIso_inv {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (f r) := by
  have h := congrArg (fun g : CommRingCat.of R ⟶ _ => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h.symm

end ScalarReadAux

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_snd_eq_coeffMap_C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ⊤))]
    (a : ↥Pl) :
    ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ⊤)
        ((gA.app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap Pl.subtype (HahnSeries.C a) := by

  have h1 : 𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ⊤)
      ((gA.app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))) =
      (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom
        ((𝔛.Meta.toBase ≫ barPt Pl).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) := by
    exact ScalarReadAux.germToFunctionField_app_appTop_eq_of_comp_eq gA _ _ hgA₂ _

  have h2 : (𝔛.Meta.C.presheaf.germ ⊤ (genericPoint 𝔛.Meta.C) trivial).hom
        ((𝔛.Meta.toBase ≫ barPt Pl).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) =
      AlgebraicCurve.baseToFunctionField 𝔛.Meta.toBase (a : AlgebraicClosure ℚ) := by
    rw [ScalarReadAux.appTop_comp_apply, show (barPt Pl).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (a : AlgebraicClosure ℚ) from
      ScalarReadAux.appTop_specMap_ΓSpecIso_inv Pl.subtype a]
    rfl
  rw [h1, h2, show 𝔛.Meta.ffEquiv.symm (AlgebraicCurve.baseToFunctionField 𝔛.Meta.toBase (a : AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) from
    (RingEquiv.symm_apply_eq _).mpr (𝔛.Meta.ffEquiv_algebraMap _).symm]
  show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) = _
  rw [HahnSeries.C_apply, coeffMap_single, ModularCurve.algebraMap_laurentSeries_eq_single]
  rfl

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_comp_bc_app_snd_eq_coeffMap_C
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    [Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ⊤))]
    (a : ↥Pl) :
    ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ⊤)
        (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ⊤).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      coeffMap (IsLocalRing.residue ↥Pl) (HahnSeries.C a) := by
  have hcomp : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) =
      (𝔛.Mfib Pl hPl ρ hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) := by
    rw [Category.assoc, Category.assoc, hbc₂, ← Category.assoc (𝔛.comp Pl hPl ρ hρ 0), 𝔛.comp_over Pl hPl ρ hρ 0,
      ← Category.assoc, 𝔛.hefib Pl hPl ρ hρ]
  have h1 : (𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ⊤)
      (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ⊤).hom
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a))) =
      ((𝔛.Mfib Pl hPl ρ hρ).C.presheaf.germ ⊤ (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) trivial).hom
        (((𝔛.Mfib Pl hPl ρ hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) := by
    exact ScalarReadAux.germToFunctionField_app_appTop_eq_of_comp_eq _ _ _ hcomp _
  have h2 : ((𝔛.Mfib Pl hPl ρ hρ).C.presheaf.germ ⊤ (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C) trivial).hom
        (((𝔛.Mfib Pl hPl ρ hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)) =
      AlgebraicCurve.baseToFunctionField (𝔛.Mfib Pl hPl ρ hρ).toBase (IsLocalRing.residue ↥Pl a) := by
    rw [ScalarReadAux.appTop_comp_apply, ScalarReadAux.appTop_specMap_ΓSpecIso_inv (IsLocalRing.residue ↥Pl) a]
    rfl
  have h3 : (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ⊤)
      (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ⊤).hom
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)))) =
      algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) (IsLocalRing.residue ↥Pl a) := by
    exact (congrArg ((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm) (h1.trans h2)).trans
      ((RingEquiv.symm_apply_eq _).mpr ((𝔛.Mfib Pl hPl ρ hρ).ffEquiv_algebraMap _).symm)
  refine (congrArg (fun z : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) => (z : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) h3).trans ?_
  show algebraMap (IsLocalRing.ResidueField ↥Pl) (LaurentSeries (IsLocalRing.ResidueField ↥Pl)) (IsLocalRing.residue ↥Pl a) = _
  rw [HahnSeries.C_apply, coeffMap_single, ModularCurve.algebraMap_laurentSeries_eq_single]

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP coeffMap coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb jqModC xHFunctionFieldBar qExpFunctionFieldC XHDRModelAtP exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd"
namespace XHDRModelAtP
p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta_chart_nonempty w Meta efib hefib comp_over Meta_pin Mfib comp isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd"
namespace GaussStalk
p2m_open "ModularCurve.XHDRModelAtP ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve GaussStalkCore in

theorem exists_witness_of_chart
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hzU : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1 ∈ U)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U))]
    (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U))
    (hdense : ∀ W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens,
        Nonempty (Scheme.Opens.toScheme W) → Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W)))
    {C : Type} {instC : CommRing C} {instA : Algebra (R p) C} (ι : Spec (CommRingCat.of C) ⟶ X p (ΓM M H) hj)
    [IsOpenImmersion ι]
    (hι : ι ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) C)))
    (hz : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1) ∈ ι ''ᵁ ⊤)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤))))] [Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤))))]
    (lift : C → LaurentSeries (R p))
    (hB : ∀ b : C,
      ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤)))
        ((gA.app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))))) : _) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap (R p) (AlgebraicClosure ℚ)) (lift b))
    (hC : ∀ b : C,
      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤)))
        (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b)))))) : _) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      coeffMap ((IsLocalRing.residue ↥Pl).comp ρ) (lift b)) :
    ∃ (xs ys : LaurentSeries ↥Pl),
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys ≠ 0 ∧
      (((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.coeffMap Pl.subtype ys = ModularCurve.coeffMap Pl.subtype xs ∧
      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys =
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xs := by

  let eB : 𝔛.Meta.C.functionField →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (IntermediateField.val (xHFunctionFieldBar M H)).toRingHom.comp 𝔛.Meta.ffEquiv.symm.toRingHom
  let eκ : (𝔛.Mfib Pl hPl ρ hρ).C.functionField →+* LaurentSeries (IsLocalRing.ResidueField ↥Pl) :=
    (IntermediateField.val (qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))).toRingHom.comp
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom

  haveI : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ⊤)) := hdense ⊤ ⟨⟨(𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1, trivial⟩⟩
  haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ⊤)) := ⟨⟨Pbar.1, trivial⟩⟩

  obtain ⟨W, hzW, hWU, hWV, σ, τ, hσ, hτ, hunit, heq⟩ :=
    AlgebraicGeometry.exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections
      (toBase p (ΓM M H) hj) C ι hι ρ _ hz U hzU s
  haveI : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W)) := hdense W ⟨⟨_, hzW⟩⟩
  haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ W)) := ⟨⟨Pbar.1, hzW⟩⟩

  have hS : ∀ x ∈ (Set.range (fun b : C => ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
      Set.range (fun a : ↥Pl => ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map
        (homOfLE (le_top : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ ⊤)).op).hom
        ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥Pl)).inv a)))),
      ∃ w : LaurentSeries ↥Pl, reader gA eB ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) x = coeffMap Pl.subtype w ∧
        reader (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) eκ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) x = coeffMap (IsLocalRing.residue ↥Pl) w := by
    rintro x (⟨b, rfl⟩ | ⟨a, rfl⟩)
    · refine ⟨coeffMap ρ (lift b), ?_, ?_⟩
      · rw [coeffMap_coeffMap, hρ]
        exact hB b
      · rw [coeffMap_coeffMap]
        exact hC b
    · refine ⟨HahnSeries.C a, ?_, ?_⟩
      · rw [reader_res gA eB ⊤ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) le_top]
        exact ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_snd_eq_coeffMap_C
          p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ a
      · rw [reader_res (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) eκ ⊤ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) le_top]
        exact ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_comp_bc_app_snd_eq_coeffMap_C
          p M hpM H Pl hPl hj 𝔛 ρ hρ bc hbc₁ hbc₂ a
  exact GaussStalkCore.exists_witness gA (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) eB eκ (coeffMap Pl.subtype) (coeffMap (IsLocalRing.residue ↥Pl))
    U ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) W hWU hWV _ hS σ τ hσ hτ hunit s heq

end ModularCurve.XHDRModelAtP.GaussStalk

namespace ModularCurve p2m_export "ModularCurve" "JZeroNeronObjectAtP coeffMap coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb jqModC xHFunctionFieldBar qExpFunctionFieldC XHDRModelAtP exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd" namespace XHDRModelAtP p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta_chart_nonempty w Meta efib hefib comp_over Meta_pin Mfib comp isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaInf_eq_coeffMap_of_mfib_of_not_sq_dvd" namespace GaussStalk end ModularCurve.XHDRModelAtP.GaussStalk
p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open Classical _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve in

theorem ModularCurve.XHDRModelAtP.GaussStalk.exists_witness_fin
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hzU : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1 ∈ U)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U))]
    (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U))
    (hdense : ∀ W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens,
        Nonempty (Scheme.Opens.toScheme W) → Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W)))
    (hz : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1) ∈ (ιFin p (ΓM M H) hj) ''ᵁ ⊤) :
    ∃ (xs ys : LaurentSeries ↥Pl),
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys ≠ 0 ∧
      (((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.coeffMap Pl.subtype ys = ModularCurve.coeffMap Pl.subtype xs ∧
      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys =
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xs := by
  haveI : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))) := hdense _ ⟨⟨_, hz⟩⟩
  haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))) := ⟨⟨Pbar.1, hz⟩⟩
  have hint := ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ _)
  have hBc : ∀ b : ↥(chartAlgFin p (ΓM M H) hj),
      ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))
        ((gA.app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b))))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap (R p) (AlgebraicClosure ℚ)) (Classical.choose (hint.1 b)) := fun b => by
    rw [ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_fst_iotaFin_eq_coeffEmb
        p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ b, IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ), ← coeffMap_coeffMap,
        Classical.choose_spec (hint.1 b)]
    rfl
  have hCc : ∀ b : ↥(chartAlgFin p (ΓM M H) hj),
      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))
        (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv b)))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      coeffMap ((IsLocalRing.residue ↥Pl).comp ρ) (Classical.choose (hint.1 b)) := fun b =>
    ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_comp_bc_app_fst_iotaFin_eq_coeffMap
        p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ bc hbc₁ b _ (Classical.choose_spec (hint.1 b))
  exact @ModularCurve.XHDRModelAtP.GaussStalk.exists_witness_of_chart p _ M _ hpM H Pl hPl _ _ hj 𝔛 ρ hρ
    gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar U hzU _ _ s hdense _ _ _ (ιFin p (ΓM M H) hj) _
    (TwoChartIntegralModel.ιFin_toBase _ _ _) hz _ _ (fun b => Classical.choose (hint.1 b)) hBc hCc

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open Classical _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve in

theorem ModularCurve.XHDRModelAtP.GaussStalk.exists_witness_inf
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))
    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hzU : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1 ∈ U)
    [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U))]
    (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U))
    (hdense : ∀ W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens,
        Nonempty (Scheme.Opens.toScheme W) → Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W)))
    (hz : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1) ∈ (ιInf p (ΓM M H) hj) ''ᵁ ⊤) :
    ∃ (xs ys : LaurentSeries ↥Pl),
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys ≠ 0 ∧
      (((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.coeffMap Pl.subtype ys = ModularCurve.coeffMap Pl.subtype xs ∧
      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys =
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xs := by
  haveI : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))) := hdense _ ⟨⟨_, hz⟩⟩
  haveI : Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))) := ⟨⟨Pbar.1, hz⟩⟩
  have hint := ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ _)
  have hBc : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))
        ((gA.app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b))))) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap (R p) (AlgebraicClosure ℚ)) (Classical.choose (hint.2 b)) := fun b => by
    rw [ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_fst_iotaInf_eq_coeffEmb
        p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ b, IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ), ← coeffMap_coeffMap,
        Classical.choose_spec (hint.2 b)]
    rfl
  have hCc : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))
        (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b)))))) : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      coeffMap ((IsLocalRing.residue ↥Pl).comp ρ) (Classical.choose (hint.2 b)) := fun b =>
    ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_comp_bc_app_fst_iotaInf_eq_coeffMap
        p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ bc hbc₁ b _ (Classical.choose_spec (hint.2 b))
  exact @ModularCurve.XHDRModelAtP.GaussStalk.exists_witness_of_chart p _ M _ hpM H Pl hPl _ _ hj 𝔛 ρ hρ
    gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar U hzU _ _ s hdense _ _ _ (ιInf p (ΓM M H) hj) _
    (TwoChartIntegralModel.ιInf_toBase _ _ _) hz _ _ (fun b => Classical.choose (hint.2 b)) hBc hCc

open Classical in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens.ModularCurve in

theorem solution

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (Pbar : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hzU : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
    (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
    (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U)))
      (xs ys : LaurentSeries ↥Pl),

      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys ≠ 0 ∧
      (((𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
          ModularCurve.coeffMap Pl.subtype ys = ModularCurve.coeffMap Pl.subtype xs ∧

      ((((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) :
          LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) ys =
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xs ∧

      (IsUnit s → ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord
        ((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) = 0) := by
  have hPt : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1 ∈ U := hzU
  haveI hneU : Nonempty (Scheme.Opens.toScheme ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U)) := ⟨⟨Pbar.1, hPt⟩⟩
  refine ⟨hneU, ?_⟩
  have hdense := (ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
    p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂).2.1
  have hUnit : IsUnit s → ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord
      ((𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U)
        (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s))) = 0 := fun hs =>
    AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
      (𝔛.Mfib Pl hPl ρ hρ) ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) Pbar hPt _ (hs.map _)
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1)) with ⟨y, hy⟩ | ⟨y, hy⟩
  · have hz : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1) ∈ (ιFin p (ΓM M H) hj) ''ᵁ ⊤ := by
      rw [Scheme.Hom.image_top_eq_opensRange]; exact ⟨y, hy⟩
    have key := ModularCurve.XHDRModelAtP.GaussStalk.exists_witness_fin p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ
      gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar U hPt s hdense hz
    exact key.elim fun xs hx => hx.elim fun ys h => ⟨xs, ys, h.1, h.2.1, h.2.2, hUnit⟩
  · have hz : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base Pbar.1) ∈ (ιInf p (ΓM M H) hj) ''ᵁ ⊤ := by
      rw [Scheme.Hom.image_top_eq_opensRange]; exact ⟨y, hy⟩
    have key := ModularCurve.XHDRModelAtP.GaussStalk.exists_witness_inf p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ
      gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar U hPt s hdense hz
    exact key.elim fun xs hx => hx.elim fun ys h => ⟨xs, ys, h.1, h.2.1, h.2.2, hUnit⟩

end S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens (solution)
