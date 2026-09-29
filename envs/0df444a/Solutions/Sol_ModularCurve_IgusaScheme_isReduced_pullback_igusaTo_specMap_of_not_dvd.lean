-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isReduced_pullback_igusaTo_specMap_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5619f045-c525-5838-b469-37553fc5a25d

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

noncomputable section

namespace RedFibreAlgebra

set_option synthInstance.maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

scoped instance span_int_isPrime : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)

scoped instance dvr : IsDiscreteValuationRing ℤp :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out

scoped instance isLoc : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) :=
  GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out

theorem irreducible_p : Irreducible ((p : ℕ) : ℤp) :=
  GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out

theorem isMaximal_span_p : (Ideal.span {((p : ℕ) : ℤp)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_p p)

private theorem _root_.RedFibreAlgebra.ringHom_ext {S : Type*} [CommRing S] (f g : ℤp →+* S) : f = g :=
  IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

p2m_export "RedFibreAlgebra" "ringHom_ext"

def φ : ℤp →+* ZMod p :=
  IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) (S := ℤp)
    (g := Int.castRingHom (ZMod p)) (by
      rintro ⟨y, hy⟩
      have hy0 : (y : ZMod p) ≠ 0 := by
        intro h
        apply hy
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
        exact Ideal.mem_span_singleton.mpr h
      exact isUnit_iff_ne_zero.mpr hy0)

theorem φ_surjective : Function.Surjective (φ p) := ZMod.ringHom_surjective _

theorem isReduced_tensor_of_eq_zero (B : Type*) [CommRing B] [Algebra ℤp B]
    [IsReduced (B ⧸ Ideal.span {((p : ℕ) : B)})]
    (L : Type*) [Field L] [Algebra ℤp L] (hL : algebraMap ℤp L p = 0) :
    IsReduced (B ⊗[ℤp] L) := by
  let e6 : L ⊗[ℤp] B ≃ₐ[ℤp] B ⊗[ℤp] L := Algebra.TensorProduct.comm ℤp L B
  haveI : CharP L p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by
    rw [← map_natCast (algebraMap ℤp L), hL])
  letI : Algebra ℤp (ZMod p) := (φ p).toAlgebra
  letI : Algebra (ZMod p) L := ZMod.algebra L p
  haveI : IsScalarTower ℤp (ZMod p) L :=
    IsScalarTower.of_algebraMap_eq' (ringHom_ext p _ _)

  let I : Ideal ℤp := RingHom.ker (Algebra.ofId ℤp (ZMod p))
  have hsurj : Function.Surjective (Algebra.ofId ℤp (ZMod p)) := φ_surjective p
  have hI : I = Ideal.span {((p : ℕ) : ℤp)} := by
    refine ((isMaximal_span_p p).eq_of_le (RingHom.ker_ne_top _) ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast,
      ZMod.natCast_self]

  let e1 : (ℤp ⧸ I) ≃ₐ[ℤp] ZMod p := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let e2 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  have hIB : I.map (algebraMap ℤp B) = Ideal.span {((p : ℕ) : B)} := by
    rw [hI, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI r1 : IsReduced (B ⧸ I.map (algebraMap ℤp B)) := by
    let e := Ideal.quotEquivOfEq hIB
    exact isReduced_of_injective e e.injective
  haveI r2 : IsReduced (B ⊗[ℤp] (ℤp ⧸ I)) :=
    isReduced_of_injective e2.symm e2.symm.injective
  let e3 := (Algebra.TensorProduct.comm ℤp B (ℤp ⧸ I)).trans
      (Algebra.TensorProduct.congr e1 (AlgEquiv.refl (R := ℤp) (A₁ := B)))
  haveI r3 : IsReduced (ZMod p ⊗[ℤp] B) :=
    isReduced_of_injective e3.symm e3.symm.injective

  haveI r4 : IsReduced (L ⊗[ZMod p] (ZMod p ⊗[ℤp] B)) :=
    Algebra.isReduced_tensorProduct_of_perfectField (ZMod p) (ZMod p ⊗[ℤp] B) L
  let e5 := Algebra.TensorProduct.cancelBaseChange ℤp (ZMod p) (ZMod p) L B
  haveI r5 : IsReduced (L ⊗[ℤp] B) :=
    isReduced_of_injective e5.symm e5.symm.injective
  exact isReduced_of_injective e6.symm e6.symm.injective

theorem injective_algebraMap_of_ne_zero (L : Type*) [Field L] [Algebra ℤp L]
    (hL : algebraMap ℤp L p ≠ 0) : Function.Injective (algebraMap ℤp L) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 (irreducible_p p)
  rw [map_mul, map_pow] at hr
  have hu : IsUnit (algebraMap ℤp L (u : ℤp)) := (Units.isUnit u).map _
  exact pow_ne_zero n hL ((hu.mul_right_eq_zero).mp hr)

theorem isReduced_tensor_of_ne_zero (B : Type*) [CommRing B] [Algebra ℤp B] [IsReduced B]
    (L : Type*) [Field L] [Algebra ℤp L] (hL : algebraMap ℤp L p ≠ 0) :
    IsReduced (B ⊗[ℤp] L) := by

  have key : IsReduced (L ⊗[ℤp] B) := by
    haveI : IsFractionRing ℤp ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
    have hinj := injective_algebraMap_of_ne_zero p L hL
    letI : Algebra ℚ L := (IsFractionRing.lift hinj : ℚ →+* L).toAlgebra
    haveI : IsScalarTower ℤp ℚ L :=
      IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinj x).symm

    haveI r1 : IsReduced (B ⊗[ℤp] ℚ) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤp))
        (B ⊗[ℤp] ℚ) inferInstance
    let e2 := Algebra.TensorProduct.comm ℤp B ℚ
    haveI r2 : IsReduced (ℚ ⊗[ℤp] B) := isReduced_of_injective e2.symm e2.symm.injective

    haveI r3 : IsReduced (L ⊗[ℚ] (ℚ ⊗[ℤp] B)) :=
      Algebra.isReduced_tensorProduct_of_perfectField ℚ (ℚ ⊗[ℤp] B) L
    let e4 := Algebra.TensorProduct.cancelBaseChange ℤp ℚ ℚ L B
    exact isReduced_of_injective e4.symm e4.symm.injective
  let e5 := Algebra.TensorProduct.comm ℤp L B
  exact isReduced_of_injective e5.symm e5.symm.injective

theorem isReduced_tensor (B : Type*) [CommRing B] [Algebra ℤp B] [IsReduced B]
    [IsReduced (B ⧸ Ideal.span {((p : ℕ) : B)})]
    (L : Type*) [Field L] [Algebra ℤp L] : IsReduced (B ⊗[ℤp] L) := by
  by_cases hL : algebraMap ℤp L p = 0
  · exact isReduced_tensor_of_eq_zero p B L hL
  · exact isReduced_tensor_of_ne_zero p B L hL

end RedFibreAlgebra
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd.RedFibreAlgebra"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd.RedFibreAlgebra"

noncomputable section

namespace RedFibreGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
variable (L : Type u) [CommRing L] [Algebra R L]

theorem isReduced_pullback_specMap
    (H : ∀ x : X, ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (h : Spec (.of B) ⟶ X) (_ : IsOpenImmersion h),
      h ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ x ∈ Set.range h ∧
        IsReduced (B ⊗[R] L)) :
    IsReduced (pullback f (Scheme.TwoAffineOpenCover.specMap R L)) := by
  have hst : ∀ z : ↥(pullback f (Scheme.TwoAffineOpenCover.specMap R L)),
      _root_.IsReduced ((pullback f (Scheme.TwoAffineOpenCover.specMap R L)).presheaf.stalk z) := by
    intro z
    obtain ⟨B, _, _, h, _, hh, hx, hred⟩ := H ((pullback.fst f _ : pullback f _ ⟶ X) z)

    let g := Scheme.TwoAffineOpenCover.specMap R L
    haveI : IsReduced (Spec (.of (B ⊗[R] L))) := by
      haveI : _root_.IsReduced (CommRingCat.of (B ⊗[R] L)) := hred
      infer_instance
    haveI hU : IsReduced (pullback (h ≫ f) g) :=
      isReduced_of_isOpenImmersion ((pullback.congrHom hh rfl).hom ≫ (pullbackSpecIso R B L).hom)
    let i := pullback.map (h ≫ f) g f g h (𝟙 _) (𝟙 _) (by simp) (by simp)
    have hz : z ∈ Set.range i := by
      rw [Scheme.Pullback.range_map]
      exact ⟨hx, by simp⟩
    obtain ⟨y, rfl⟩ := hz
    exact isReduced_of_injective _ (asIso <| i.stalkMap y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

end RedFibreGeometry
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd.RedFibreAlgebra"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd.RedFibreAlgebra"

noncomputable section

namespace RedFibreIgusa

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

set_option synthInstance.maxHeartbeats 1600000

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem isReduced_chartFin_tensor (hpN : ¬ p ∣ N) (L : Type) [Field L] [Algebra ℤp L] :
    IsReduced (↥(chartAlgFin (N * p) p) ⊗[ℤp] L) := by
  haveI := (isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd N p hpN).1
  exact RedFibreAlgebra.isReduced_tensor p _ L

theorem isReduced_chartInf_tensor (hpN : ¬ p ∣ N) (L : Type) [Field L] [Algebra ℤp L] :
    IsReduced (↥(chartAlgInf (N * p) p) ⊗[ℤp] L) := by
  haveI := (isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd N p hpN).2.2.1
  exact RedFibreAlgebra.isReduced_tensor p _ L

theorem isReduced_fibre (hpN : ¬ p ∣ N) (L : Type) [Field L] [Algebra ℤp L] :
    IsReduced (pullback (igusaTo (N * p) p)
      (Scheme.TwoAffineOpenCover.specMap ℤp L)) := by
  refine RedFibreGeometry.isReduced_pullback_specMap (igusaTo (N * p) p) L fun x => ?_
  rcases mem_range_ιFin_or_mem_range_ιInf (N * p) p x with hx | hx
  · exact ⟨_, inferInstance, inferInstance, ιFin (N * p) p, inferInstance, ιFin_igusaTo (N * p) p,
      hx, isReduced_chartFin_tensor N p hpN L⟩
  · exact ⟨_, inferInstance, inferInstance, ιInf (N * p) p, inferInstance, ιInf_igusaTo (N * p) p,
      hx, isReduced_chartInf_tensor N p hpN L⟩

end RedFibreIgusa
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd.RedFibreAlgebra"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd.RedFibreAlgebra"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [Algebra ↥(GaloisRep.ratLocalizedAt p) L] :
    IsReduced (pullback (igusaTo (N * p) p)
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) L)) :=
  RedFibreIgusa.isReduced_fibre N p hpN L

end S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd (solution)
