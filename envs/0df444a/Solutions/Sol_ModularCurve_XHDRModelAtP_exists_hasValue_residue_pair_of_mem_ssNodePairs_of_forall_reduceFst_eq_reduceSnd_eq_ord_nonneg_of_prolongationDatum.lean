-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/104d31db-1bbb-5c6f-8b34-ba004614ec9f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_primes_tensorProduct_chartAlgFin_crossing_gauss_iff_and_section_and_hasValue
import Theorems.Thm_Localization_AtPrime_mem_range_of_forall_branch_of_forall_comap_eq_bot_and_valuation_dichotomy_of_map_eq_iInf_tensorProduct_valuationSubring_of_liesOverPrime
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
import Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.XHDRLevel.bcMap_fst ModularCurve.XHDRLevel.bcMap_snd_assoc ModularCurve.XHDRLevel.bcMap_fst_assoc ModularCurve.XHDRLevel.bcMap_snd ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

open scoped TensorProduct

noncomputable section

namespace NodeRegSkel

open ModularCurve AlgebraicCurve

section Gamma

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}

variable (p M H hj) in

def toF : ↥(chartAlgFin p (ΓM M H) hj) →+* ↥(xHFunctionFieldBar M H) :=
  RingHom.codRestrict
    ((coeffEmb (AlgebraicClosure ℚ)).comp
      ((qExpFunctionFieldC ℚ (ΓM M H)).toSubalgebra.toSubring.subtype.comp (chartAlgFin p (ΓM M H) hj).toSubring.subtype))
    (xHFunctionFieldBar M H)
    (fun b => coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2)

@[scoped simp] theorem coe_toF (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    ((toF p M H hj b : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := rfl

variable (M H) in

def constF (Pl : ValuationSubring (AlgebraicClosure ℚ)) : ↥Pl →+* ↥(xHFunctionFieldBar M H) :=
  (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp Pl.subtype

variable (p M H hj) in

def gammaFin (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥Pl) [Algebra (R p) ↥Pl]
    (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (halg : algebraMap (R p) ↥Pl = ρ) : ↥Pl ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj) →+* ↥(xHFunctionFieldBar M H) := by
  letI : Algebra (R p) ↥(xHFunctionFieldBar M H) := ((constF M H Pl).comp (algebraMap (R p) ↥Pl)).toAlgebra
  refine (Algebra.TensorProduct.lift (⟨constF M H Pl, fun _ => rfl⟩ : ↥Pl →ₐ[R p] ↥(xHFunctionFieldBar M H))
    (⟨toF p M H hj, fun r => ?_⟩ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(xHFunctionFieldBar M H)) (fun _ _ => Commute.all _ _)).toRingHom

  apply Subtype.ext
  change ((toF p M H hj (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) r) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
    ((constF M H Pl (algebraMap (R p) ↥Pl r) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
  rw [coe_toF]
  have h1 : (((algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) r : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) := by
    rw [Subalgebra.coe_algebraMap]
    have : algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) r = algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) (r : ℚ) := rfl
    rw [this, eq_ratCast, eq_ratCast]
    exact SubfieldClass.coe_ratCast _ _
  have h2 : ((constF M H Pl (algebraMap (R p) ↥Pl r) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ρ r : ↥Pl) : AlgebraicClosure ℚ) := by
    rw [halg]; rfl
  rw [h1, h2, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single]
  have h3 : ((ρ r : ↥Pl) : AlgebraicClosure ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) r := by
    have := congrArg (fun φ => φ r) hρ; simpa using this
  rw [h3]
  change coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (HahnSeries.single 0 (r : ℚ)) = _
  rw [coeffMap_single]
  rfl

theorem gammaFin_tmul (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥Pl) [Algebra (R p) ↥Pl]
    (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (halg : algebraMap (R p) ↥Pl = ρ)
    (α : ↥Pl) (b : ↥(chartAlgFin p (ΓM M H) hj)) :
    ((gammaFin p M H hj Pl ρ hρ halg (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by
  unfold gammaFin
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, AlgHom.coe_mk]
  rw [show ((constF M H Pl α * toF p M H hj b : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
    ((constF M H Pl α : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
      ((toF p M H hj b : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) from rfl]
  rw [coe_toF]
  have hc : ((constF M H Pl α : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      HahnSeries.C (α : AlgebraicClosure ℚ) := by
    change ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (α : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) :
      LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (α : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) α from rfl,
      algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  rw [hc, HahnSeries.C_mul_eq_smul]

end Gamma

theorem isFractionRing_of_injective_of_forall_exists
    {T : Type*} [CommRing T] [IsDomain T] (𝔔 : Ideal T) [𝔔.IsPrime]
    {F : Type*} [Field F] (γ : T →+* F) (hγ : Function.Injective γ)
    (hfrac : ∀ e : F, ∃ a s : T, s ≠ 0 ∧ e * γ s = γ a)
    [Algebra (Localization.AtPrime 𝔔) F]
    (halg : ∀ t : T, algebraMap (Localization.AtPrime 𝔔) F (algebraMap T _ t) = γ t) :
    IsFractionRing (Localization.AtPrime 𝔔) F := by
  classical
  have hle : 𝔔.primeCompl ≤ nonZeroDivisors T := by
    intro s hs
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => hs (h0 ▸ 𝔔.zero_mem))
  haveI : IsDomain (Localization.AtPrime 𝔔) := IsLocalization.isDomain_localization hle
  have hγ0 : ∀ s : T, s ≠ 0 → γ s ≠ 0 := fun s hs h => hs (hγ (by rw [h, map_zero]))
  have hmk : ∀ (a : T) (s : 𝔔.primeCompl),
      algebraMap (Localization.AtPrime 𝔔) F (IsLocalization.mk' _ a s) * γ s = γ a := by
    intro a s
    rw [← halg s, ← map_mul, IsLocalization.mk'_spec, halg]
  have hinjS : Function.Injective (algebraMap (Localization.AtPrime 𝔔) F) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl x
    have h1 := hmk a s
    simp only at hx
    rw [hx, zero_mul] at h1
    have ha : a = 0 := hγ (by rw [← h1, map_zero])
    simp [ha]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    apply IsUnit.mk0
    rw [map_ne_zero_iff _ hinjS]
    exact nonZeroDivisors.ne_zero y.2
  · intro e
    obtain ⟨a, s, hs, he⟩ := hfrac e
    refine ⟨⟨algebraMap T _ a, ⟨algebraMap T _ s, ?_⟩⟩, ?_⟩
    · exact mem_nonZeroDivisors_of_ne_zero
        (IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ hle (mem_nonZeroDivisors_of_ne_zero hs))
    · simp only [halg]
      exact he
  · intro x y hxy
    exact ⟨1, by simpa using hinjS hxy⟩

theorem finiteType_chartAlgFin (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Algebra.FiniteType (R p) ↥(chartAlgFin p (ΓM M H) hj) :=
  haveI : (ΓM M H).FiniteIndex := CuspForm.GammaH_finiteIndex M H
  (ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p (ΓM M H)
    (ModularCurve.translation_mem_GammaH M H) (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1

theorem flat_chartAlgFin (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Module.Flat (R p) ↥(chartAlgFin p (ΓM M H) hj) := by
  haveI := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI := IsPrincipalIdealRing.isDedekindDomain (R p)
  have hinjF : Function.Injective (algebraMap (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    intro a b h
    have : (algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H)) (a : ℚ)) = algebraMap ℚ _ (b : ℚ) := h
    exact Subtype.ext ((algebraMap ℚ ↥(qExpFunctionFieldC ℚ (ΓM M H))).injective this)
  haveI : Module.IsTorsionFree (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjF
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

section ord
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hk, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 k)

end ord

theorem base_inv_base_apply {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (y : Y) : f.base ((inv f).base y) = y := by
  show ((inv f) ≫ f).base y = y
  rw [IsIso.inv_hom_id]; rfl

theorem coe_residue_mul_coeffMap_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers)
    (x' y' : LaurentSeries ↥A)
    (hx' : coeffMap A.subtype x' ∈ xHFunctionFieldBar M H) (hy' : coeffMap A.subtype y' ∈ xHFunctionFieldBar M H)
    (hfy : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y' = coeffMap A.subtype x') :
    ((Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) *
        coeffMap (IsLocalRing.residue ↥A) y' = coeffMap (IsLocalRing.residue ↥A) x' := by
  obtain ⟨hyO, hyres⟩ := Rpd.residue₁_coeffMap y' hy'
  obtain ⟨hxO, hxres⟩ := Rpd.residue₁_coeffMap x' hx'
  have hmul : (⟨f, h₁⟩ : Rpd.R₁.integers) * ⟨⟨coeffMap A.subtype y', hy'⟩, hyO⟩ = ⟨⟨coeffMap A.subtype x', hx'⟩, hxO⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hfy
  have h := congrArg (fun z => ((Rpd.R₁.residue z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :
      LaurentSeries (ResidueField ↥A))) hmul
  simp only [map_mul] at h
  rw [← hyres, ← hxres]
  simpa using h

theorem regular_of_branches_of_horizontal
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Algebra.FiniteType (R p) B] [Module.Flat (R p) B]
    (γ : (↥A ⊗[R p] B) →+* ↥(xHFunctionFieldBar M H))
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] B), s ≠ 0 ∧ e * γ s = γ a)
    (𝔔 𝔯₀ 𝔯₁ : Ideal (↥A ⊗[R p] B)) (h𝔔 : 𝔔.IsPrime) (h𝔯₀ : 𝔯₀.IsPrime) (h𝔯₁ : 𝔯₁.IsPrime)
    (hle₀ : 𝔯₀ ≤ 𝔔) (hle₁ : 𝔯₁ ≤ 𝔔) (hnc₀₁ : ¬ 𝔯₀ ≤ 𝔯₁) (hnc₁₀ : ¬ 𝔯₁ ≤ 𝔯₀)
    (h𝔔A : 𝔔.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := B)) =
      IsLocalRing.maximalIdeal ↥A)
    (hbr : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := B)) = 𝔯₀ ⊓ 𝔯₁)
    (f : ↥(xHFunctionFieldBar M H))
    (hb₀ : ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔯₀ ∧ f * γ c = γ a)
    (hb₁ : ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔯₁ ∧ f * γ c = γ a)
    (hhor : ∀ 𝔮 : Ideal (↥A ⊗[R p] B), 𝔮.IsPrime →
      𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := B)) = ⊥ → 𝔮 ≠ ⊥ → 𝔮 ≤ 𝔔 →
      ∃ a s : (↥A ⊗[R p] B), s ∉ 𝔮 ∧ f * γ s = γ a) :
    ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔔 ∧ f * γ c = γ a := by
  classical
  haveI := h𝔔

  haveI hTdom : IsDomain (↥A ⊗[R p] B) := hγinj.isDomain γ

  haveI hSdom : IsDomain (Localization.AtPrime 𝔔) := IsLocalization.isDomain_localization 𝔔.primeCompl_le_nonZeroDivisors
  have hγne : ∀ c : 𝔔.primeCompl, IsUnit (γ c) := fun c =>
    ((map_ne_zero_iff _ hγinj).mpr (fun h => c.2 (by rw [h]; exact 𝔔.zero_mem))).isUnit
  letI algSF : Algebra (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) := (IsLocalization.lift (M := 𝔔.primeCompl) hγne).toAlgebra
  have halgSF : ∀ c : (↥A ⊗[R p] B),
      algebraMap (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) (algebraMap _ (Localization.AtPrime 𝔔) c) = γ c :=
    fun c => IsLocalization.lift_eq (M := 𝔔.primeCompl) hγne c
  haveI hfracSF : IsFractionRing (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) :=
    isFractionRing_of_injective_of_forall_exists 𝔔 γ hγinj hγfrac halgSF

  have hincl : (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom =
      Algebra.TensorProduct.includeLeftRingHom := RingHom.ext fun _ => rfl
  have h𝔔A' : 𝔔.comap (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A)
      (B := B)).toRingHom = IsLocalRing.maximalIdeal ↥A := by rw [hincl]; exact h𝔔A

  have hd₀ : Disjoint (𝔔.primeCompl : Set (↥A ⊗[R p] B)) ↑𝔯₀ := Set.disjoint_left.mpr fun x hx hx' => hx (hle₀ hx')
  have hd₁ : Disjoint (𝔔.primeCompl : Set (↥A ⊗[R p] B)) ↑𝔯₁ := Set.disjoint_left.mpr fun x hx hx' => hx (hle₁ hx')
  let 𝔯S : Fin 2 → Ideal (Localization.AtPrime 𝔔) :=
    ![𝔯₀.map (algebraMap _ (Localization.AtPrime 𝔔)), 𝔯₁.map (algebraMap _ (Localization.AtPrime 𝔔))]
  have h𝔯S0 : 𝔯S 0 = 𝔯₀.map (algebraMap _ (Localization.AtPrime 𝔔)) := rfl
  have h𝔯S1 : 𝔯S 1 = 𝔯₁.map (algebraMap _ (Localization.AtPrime 𝔔)) := rfl
  have hu₀ : (𝔯₀.map (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔))).comap (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)) = 𝔯₀ :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔔.primeCompl (Localization.AtPrime 𝔔) h𝔯₀ hd₀
  have hu₁ : (𝔯₁.map (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔))).comap (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)) = 𝔯₁ :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔔.primeCompl (Localization.AtPrime 𝔔) h𝔯₁ hd₁
  have h𝔯S : ∀ i, (𝔯S i).IsPrime := by
    intro i
    fin_cases i
    · exact IsLocalization.isPrime_of_isPrime_disjoint 𝔔.primeCompl (Localization.AtPrime 𝔔) 𝔯₀ h𝔯₀ hd₀
    · exact IsLocalization.isPrime_of_isPrime_disjoint 𝔔.primeCompl (Localization.AtPrime 𝔔) 𝔯₁ h𝔯₁ hd₁
  have h𝔯Smin : ∀ i j, 𝔯S i ≤ 𝔯S j → 𝔯S i = 𝔯S j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso; apply hnc₀₁
      have := Ideal.comap_mono (f := algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)) hij
      simpa only [𝔯S, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hu₀, hu₁] using this
    · exfalso; apply hnc₁₀
      have := Ideal.comap_mono (f := algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)) hij
      simpa only [𝔯S, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hu₀, hu₁] using this
    · rfl
  have hinf : (⨅ i, 𝔯S i) = 𝔯S 0 ⊓ 𝔯S 1 :=
    le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1)) (le_iInf fun i => by fin_cases i <;> simp)
  have h𝔭S : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)).comp
      (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) = ⨅ i, 𝔯S i := by
    rw [hincl, ← Ideal.map_map, hbr, IsLocalization.map_inf 𝔔.primeCompl (Localization.AtPrime 𝔔), hinf]
    rfl

  obtain ⟨hLU, -⟩ :=
    Localization.AtPrime.mem_range_of_forall_branch_of_forall_comap_eq_bot_and_valuation_dichotomy_of_map_eq_iInf_tensorProduct_valuationSubring_of_liesOverPrime
      p A hA ρ hρ halg B 𝔔 h𝔔A' 𝔯S h𝔯S h𝔯Smin h𝔭S ↥(xHFunctionFieldBar M H)

  have toS_not_mem : ∀ (I : Ideal (↥A ⊗[R p] B)) (hI : (I.map (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔))).comap (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)) = I)
      (c : (↥A ⊗[R p] B)), c ∉ I → algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔) c ∉ I.map (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)) := by
    intro I hI c hc hc'
    apply hc
    rw [← hI]
    exact hc'
  have hbS : ∀ i, ∃ a c : Localization.AtPrime 𝔔, c ∉ 𝔯S i ∧
      f * algebraMap (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) c = algebraMap (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) a := by
    intro i
    fin_cases i
    · obtain ⟨a, c, hc, hfac⟩ := hb₀
      exact ⟨algebraMap _ _ a, algebraMap _ _ c, toS_not_mem 𝔯₀ hu₀ c hc, by rw [halgSF, halgSF]; exact hfac⟩
    · obtain ⟨a, c, hc, hfac⟩ := hb₁
      exact ⟨algebraMap _ _ a, algebraMap _ _ c, toS_not_mem 𝔯₁ hu₁ c hc, by rw [halgSF, halgSF]; exact hfac⟩

  have hhorS : ∀ 𝔮S : Ideal (Localization.AtPrime 𝔔), 𝔮S.IsPrime →
      𝔮S.comap ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) = ⊥ →
      ∃ a s : Localization.AtPrime 𝔔, s ∉ 𝔮S ∧
        f * algebraMap (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) s = algebraMap (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) a := by
    intro 𝔮S h𝔮S hbotS
    obtain ⟨h𝔮, hdisj⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint 𝔔.primeCompl (Localization.AtPrime 𝔔) 𝔮S).mp h𝔮S
    set 𝔮 : Ideal (↥A ⊗[R p] B) := 𝔮S.comap (algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔔)) with h𝔮def
    have hle : 𝔮 ≤ 𝔔 := fun x hx => by
      by_contra hx'
      exact Set.disjoint_left.mp hdisj hx' hx
    have hbot : 𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := B)) = ⊥ := by
      rw [h𝔮def, Ideal.comap_comap, ← hincl]
      exact hbotS
    have lift : ∀ a s : (↥A ⊗[R p] B), s ∉ 𝔮 → f * γ s = γ a →
        ∃ a s : Localization.AtPrime 𝔔, s ∉ 𝔮S ∧
          f * algebraMap (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) s = algebraMap (Localization.AtPrime 𝔔) ↥(xHFunctionFieldBar M H) a := by
      intro a s hs hfac
      exact ⟨algebraMap _ _ a, algebraMap _ _ s, fun h => hs (by rw [h𝔮def]; exact h), by rw [halgSF, halgSF]; exact hfac⟩
    by_cases hq0 : 𝔮 = ⊥
    · obtain ⟨a, s, hs, hfac⟩ := hγfrac f
      exact lift a s (by rw [hq0]; simpa using hs) hfac
    · obtain ⟨a, s, hs, hfac⟩ := hhor 𝔮 h𝔮 hbot hq0 hle
      exact lift a s hs hfac

  obtain ⟨z, hz⟩ := hLU f hbS hhorS
  obtain ⟨a, c, rfl⟩ := IsLocalization.exists_mk'_eq 𝔔.primeCompl z
  refine ⟨a, c, c.2, ?_⟩
  rw [← halgSF, ← halgSF, ← hz, ← map_mul, IsLocalization.mk'_spec]

set_option maxHeartbeats 3200000 in
theorem core
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), s ≠ 0 ∧ e * γ s = γ a)
    (𝔔 𝔯₀ 𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔔 : 𝔔.IsPrime) (h𝔯₀ : 𝔯₀.IsPrime) (h𝔯₁ : 𝔯₁.IsPrime)
    (hle₀ : 𝔯₀ ≤ 𝔔) (hle₁ : 𝔯₁ ≤ 𝔔) (hnc₀₁ : ¬ 𝔯₀ ≤ 𝔯₁) (hnc₁₀ : ¬ 𝔯₁ ≤ 𝔯₀)
    (h𝔔A : 𝔔.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) =
      IsLocalRing.maximalIdeal ↥A)
    (hbr : (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = 𝔯₀ ⊓ 𝔯₁)
    (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hG₀ : ∀ h : ↥(xHFunctionFieldBar M H),
        (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₀ ∧ h * γ c = γ a) ↔
        (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x))
    (hG₁ : ∀ h : ↥(xHFunctionFieldBar M H),
        (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₁ ∧ h * γ c = γ a) ↔
        (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (hHor : ∀ 𝔮 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), 𝔮.IsPrime →
        𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = ⊥ → 𝔮 ≠ ⊥ → 𝔮 ≤ 𝔔 →
        ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
          (_ : uκ ≫ pullback.snd _ _ = 𝟙 _),
          uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n ∧
          ∀ e : ↥(xHFunctionFieldBar M H), e ∈ (𝔛.Meta.pointEquivPlace y).toValuationSubring ↔ ∃ a s : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), s ∉ 𝔮 ∧ e * γ s = γ a)
    (hVal : ∀ (h : ↥(xHFunctionFieldBar M H)) (a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))), c ∉ 𝔔 → h * γ c = γ a →
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn0 A hA ρ hρ n).HasValue g (χκ a / χκ c)) ∧
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn1 A hA ρ hρ n).HasValue g (χκ a / χκ c)))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (s₁ s₂ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hOn0 : 𝔛.placeOn0 A hA ρ hρ n = s₁) (hOn1 : 𝔛.placeOn1 A hA ρ hρ n = s₂)
    (hreg : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα V = s₁ → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = s₂ → 0 ≤ V.ord f) :
    ∃ c : ResidueField ↥A,
      s₁.HasValue (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c ∧
      s₂.HasValue (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c := by
  letI instAlgFb : Algebra (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := inferInstance
  letI instFieldFb : Field (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := inferInstance
  letI instFieldFM : Field ↥(xHFunctionFieldBar M H) := inferInstance

  have hGC := ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ Psp Rpd
  have hb₀ : ∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₀ ∧ f * γ c = γ a := (hG₀ f).mpr ((hGC f).mp h₁)
  have hθ₁ : θ f ∈ Rpd.R₁.integers := (Rpd.mem_integers₂_iff f).mp h₂
  have hb₁ : ∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₁ ∧ f * γ c = γ a := (hG₁ f).mpr ((hGC (θ f)).mp hθ₁)

  have hhor : ∀ 𝔮 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), 𝔮.IsPrime →
      𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = ⊥ → 𝔮 ≠ ⊥ → 𝔮 ≤ 𝔔 →
      ∃ a s : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), s ∉ 𝔮 ∧ f * γ s = γ a := by
    intro 𝔮 h𝔮 hbot hne hle
    obtain ⟨y, u, hu, uκ, huκ₁, huκ₂, hcl, hloc⟩ := hHor 𝔮 h𝔮 hbot hne hle
    apply (hloc f).mp
    rcases eq_or_ne f 0 with hf0 | hf0
    · rw [hf0]; exact zero_mem _
    apply mem_of_ord_nonneg _ hf0
    apply hreg
    ·
      obtain ⟨-, ⟨h₀mem, h₀pl⟩⟩ := 𝔛.node_pin A hA ρ hρ n
      have hP₀ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base
          ((inv (𝔛.efib A hA ρ hρ)).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)) =
          uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
        rw [hcl]
        simp only [Scheme.Hom.comp_base, TopCat.comp_app]
        rw [base_inv_base_apply]
      have h := hcomp 0 y u hu uκ huκ₁ huκ₂ ⟨_, h₀mem⟩ hP₀
      rw [if_pos rfl] at h
      rw [← h, h₀pl]
      exact hOn0
    ·
      obtain ⟨⟨h₁mem, h₁pl⟩, -⟩ := 𝔛.node_pin A hA ρ hρ n
      have hP₁ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base
          ((inv (𝔛.efib A hA ρ hρ)).base ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)) =
          uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
        rw [hcl]
        have hc := congrArg (fun φ => φ.base n)
          (pullback.condition (f := 𝔛.comp A hA ρ hρ 0) (g := 𝔛.comp A hA ρ hρ 1))
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hc ⊢
        rw [base_inv_base_apply, hc]
      have h := hcomp 1 y u hu uκ huκ₁ huκ₂ ⟨_, h₁mem⟩ hP₁
      rw [if_neg (by decide)] at h
      rw [← h, h₁pl]
      exact hOn1

  haveI := finiteType_chartAlgFin p M H hj
  haveI : Module.Flat (R p) ↥(chartAlgFin p (ΓM M H) hj) :=
    (ModularCurve.XHDRLevel.flat_chartAlgFin_and_flat_chartAlgInf p (ΓM M H) hj).1
  obtain ⟨a, c, hc, hfac⟩ := regular_of_branches_of_horizontal p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ halg
    ↥(chartAlgFin p (ΓM M H) hj) γ hγinj hγfrac
    𝔔 𝔯₀ 𝔯₁ h𝔔 h𝔯₀ h𝔯₁ hle₀ hle₁ hnc₀₁ hnc₁₀ h𝔔A hbr f hb₀ hb₁ hhor

  refine ⟨χκ a / χκ c, ?_, ?_⟩
  ·
    obtain ⟨x, y, hy, hfxy⟩ := (hGC f).mp h₁
    obtain ⟨x', y', hx', hy', hy'0, hfxy'⟩ :=
      ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA f x y hy hfxy
    have hres := coe_residue_mul_coeffMap_eq p M H hpM A θ Psp Rpd f h₁ x' y' hx' hy' hfxy'
    have hv := (hVal f a c hc hfac).1 x' y' hy'0 hfxy' (Rpd.R₁.residue ⟨f, h₁⟩) hres
    rwa [hOn0] at hv
  ·
    obtain ⟨x, y, hy, hfxy⟩ := (hGC (θ f)).mp hθ₁
    obtain ⟨x', y', hx', hy', hy'0, hfxy'⟩ :=
      ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (θ f) x y hy hfxy
    have hres := coe_residue_mul_coeffMap_eq p M H hpM A θ Psp Rpd (θ f) hθ₁ x' y' hx' hy' hfxy'
    have hv := (hVal f a c hc hfac).2 x' y' hy'0 hfxy' (Rpd.R₁.residue ⟨θ f, hθ₁⟩) hres
    rw [Rpd.residue₂_eq f h₂, ← hOn1]
    exact hv

end NodeRegSkel
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum.NodeRegSkel"

open NodeRegSkel in
set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers), ∀ s ∈ SS,
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Psp.reduceFst α hα V = s.1 → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = s.2 → 0 ≤ V.ord f) →
      ∃ c : ResidueField ↥A,
        s.1.HasValue (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c ∧
        s.2.HasValue (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c := by
  intro f h₁ h₂ s hs hreg
  letI instAlgA : Algebra (R p) ↥A := ρ.toAlgebra
  have halg : algebraMap (R p) ↥A = ρ := rfl

  obtain ⟨hss, hs1⟩ := (mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)
  obtain ⟨n, hn⟩ : ∃ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      𝔛.nodeEquiv A hA ρ hρ n = ⟨s.2, hss⟩ := ⟨(𝔛.nodeEquiv A hA ρ hρ).symm ⟨s.2, hss⟩, Equiv.apply_symm_apply _ _⟩
  have hOn1 : 𝔛.placeOn1 A hA ρ hρ n = s.2 := by
    show ((𝔛.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p)) : Place _ _) = s.2
    rw [hn]
  have hOn0 : 𝔛.placeOn0 A hA ρ hρ n = s.1 := by
    show qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
        ((𝔛.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p)) : Place _ _) = s.1
    rw [hn, ← hs1]

  have hγ := gammaFin_tmul (p := p) (M := M) (H := H) (hj := hj) A ρ hρ halg
  generalize gammaFin p M H hj A ρ hρ halg = γ at hγ

  obtain ⟨hγinj, hγfrac, -⟩ :=
    ModularCurve.XHDRModelAtP.injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
      p M H hpM hj 𝔛 A hA ρ hρ halg (chartAlgFin p (ΓM M H) hj) (ιFin p (ΓM M H) hj)
      (TwoChartIntegralModel.ιFin_toBase _ _ _) 𝔛.Meta_chart_nonempty (fun b => 𝔛.Meta_pin b) γ hγ

  obtain ⟨𝔔, 𝔯₀, 𝔯₁, χκ, h𝔔, h𝔯₀, h𝔯₁, hle₀, hle₁, hnc₀₁, hnc₁₀, hker, hχA, -, hbr, hG₀, hG₁, hHor, hVal⟩ :=
    ModularCurve.XHDRModelAtP.exists_primes_tensorProduct_chartAlgFin_crossing_gauss_iff_and_section_and_hasValue
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ halg θ hwgen γ hγ n
  have h𝔔A : 𝔔.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) =
      IsLocalRing.maximalIdeal ↥A := by
    rw [← hker, RingHom.comap_ker, hχA]
    exact Ideal.mk_ker
  exact core p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ halg θ γ hγinj hγfrac 𝔔 𝔯₀ 𝔯₁ h𝔔 h𝔯₀ h𝔯₁ hle₀ hle₁ hnc₀₁ hnc₁₀ h𝔔A hbr
    χκ hG₀ hG₁ n hHor hVal α hα hβ δ Psp Rpd hcomp f h₁ h₂ s.1 s.2 hOn0 hOn1 hreg

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum.NodeRegSkel"

end S_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_forall_reduceFst_eq_reduceSnd_eq_ord_nonneg_of_prolongationDatum (solution)
