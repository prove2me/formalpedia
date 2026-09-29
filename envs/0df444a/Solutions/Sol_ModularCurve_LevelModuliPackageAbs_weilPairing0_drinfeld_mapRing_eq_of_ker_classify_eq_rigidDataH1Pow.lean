-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9424e42c-e165-51eb-b19e-3ecc9399f71b

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_isUnit_indepElt_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_isLevelPStructure
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_map_algHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_act_of_isSectionTransport
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_weilPairing0_toPoint_variableChange_of_isLevel_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_eq_of_baseChange_eq
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing
p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra~schemeHomOverComp"

namespace K8EQ

section Torsion

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem val_nsmul (G : RelativeGroupLaw R f) {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  conv_lhs => rw [← hx]
  rw [← G.nsmul_natural f t x.1 x.2 n]
  rfl

end Torsion

theorem nsmul_eq_one_of_comp_fst_eq {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (S : Section W)
    (r : base (T := T) ⟶ G.schemeKer q)
    (hr : r ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = S.1) :
    G.nsmul (𝟙 _) q S = G.one (𝟙 _) := by
  have hr1 : r ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 = 𝟙 _ := by
    calc r ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1
        = (r ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1) ≫
            ((G.one (𝟙 _)).1 ≫ projModelStrCR W) := by
          rw [(G.one (𝟙 _)).2, Category.comp_id]
      _ = r ≫ (pullback.snd (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ (G.one (𝟙 _)).1) ≫ projModelStrCR W := by
          simp only [Category.assoc]
      _ = r ≫ (pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ G.schemeNsmul q) ≫ projModelStrCR W := by
          rw [pullback.condition]
      _ = (r ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1) ≫ (G.schemeNsmul q ≫ projModelStrCR W) := by
          simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hr, G.schemeNsmul_over, S.2]
  apply Subtype.ext
  rw [val_nsmul, ← hr, Category.assoc, pullback.condition, ← Category.assoc, hr1, Category.id_comp]

theorem nsmul_eq_one_of_isDrinfeldBasis {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W)) {q : ℕ} (hq : 2 ≤ q) {P Q : Section W}
    (h : IsDrinfeldBasis G q P Q) :
    G.nsmul (𝟙 _) q P = G.one (𝟙 _) ∧ G.nsmul (𝟙 _) q Q = G.one (𝟙 _) := by
  have h' := (isDrinfeldBasis_iff_isDrinfeldBasisOver_id G q P Q).mp h
  obtain ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩ := RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq G hq h'
  exact ⟨nsmul_eq_one_of_comp_fst_eq G q P p hp, nsmul_eq_one_of_comp_fst_eq G q Q p' hp'⟩

section Through

variable {T : Type} [CommRing T]

theorem coords_unique {W : WeierstrassCurve.Projective T} {S : Section W} {x y x' y' : T}
    (h : IsSectionThrough S x y) (h' : IsSectionThrough S x' y') : x = x' ∧ y = y' :=
  ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).2 S S x y x' y' h h').mp rfl

theorem section_unique {W : WeierstrassCurve.Projective T} {S S' : Section W} {x y : T}
    (h : IsSectionThrough S x y) (h' : IsSectionThrough S' x y) : S = S' :=
  ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).2 S S' x y x y h h').mpr ⟨rfl, rfl⟩

def sectionThrough (W : WeierstrassCurve.Projective T) (x y : T) (h : W.toAffine.Equation x y) : Section W :=
  (((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mp h).choose

theorem sectionThrough_spec (W : WeierstrassCurve.Projective T) (x y : T) (h : W.toAffine.Equation x y) :
    IsSectionThrough (sectionThrough W x y h) x y :=
  (((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mp h).choose_spec

theorem equation_of_isSectionThrough {W : WeierstrassCurve.Projective T} {S : Section W} {x y : T}
    (h : IsSectionThrough S x y) : W.toAffine.Equation x y :=
  ((equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mpr ⟨S, h⟩

end Through

section Main

def coords (q : ℕ) [Fact q.Prime] (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T) (hq : IsUnit ((q : ℕ) : T)) (x : RawDrinfeldPair T)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q E x) : LevelPData T :=
  let h := RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit q A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq x hx
  ⟨h.1.choose, h.1.choose_spec.choose, h.2.choose, h.2.choose_spec.choose⟩

theorem coords_spec (q : ℕ) [Fact q.Prime] (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T) (hq : IsUnit ((q : ℕ) : T)) (x : RawDrinfeldPair T)
    (hx : RawDrinfeldPair.IsLevel 𝒢 q E x) :
    IsSectionThrough x.P (coords q A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq x hx).xP (coords q A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq x hx).yP ∧
    IsSectionThrough x.Q (coords q A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq x hx).xQ (coords q A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq x hx).yQ :=
  let h := RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit q A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq x hx
  ⟨h.1.choose_spec.choose_spec, h.2.choose_spec.choose_spec⟩

theorem isLevelPStructure_of_isSectionThrough (q : ℕ) [Fact q.Prime] (A₀ : Type) [CommRing A₀]
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport) (hq2 : q ≠ 2)
    {T : Type} [CommRing T] [Algebra A₀ T] (E : WeierstrassCurve T) (hq : IsUnit ((q : ℕ) : T))
    (x : RawDrinfeldPair T) (hx : RawDrinfeldPair.IsLevel 𝒢 q E x) (D : LevelPData T)
    (hP : IsSectionThrough x.P D.xP D.yP) (hQ : IsSectionThrough x.Q D.xQ D.yQ) :
    IsLevelPStructure E q D := by
  obtain ⟨hc, hΔx, hDB⟩ := hx
  have hind := RawDrinfeldPair.IsLevel.isUnit_indepElt_of_isSectionThrough q hq2 A₀ 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 E hq x
    ⟨hc, hΔx, hDB⟩ D.xP D.yP D.xQ D.yQ hP hQ
  have htors := nsmul_eq_one_of_isDrinfeldBasis (𝒢 T x.curve hΔx) (Fact.out : q.Prime).two_le hDB
  have hpreP := (nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O q hq2 T hq x.curve hΔx
    x.P D.xP D.yP hP).mp htors.1
  have hpreQ := (nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough 𝒢 h𝒢 h𝒢O q hq2 T hq x.curve hΔx
    x.Q D.xQ D.yQ hQ).mp htors.2
  subst hc
  exact ⟨equation_of_isSectionThrough hP, equation_of_isSectionThrough hQ, hpreP, hpreQ, hind.1, hind.2⟩

end Main

end K8EQ

open CategoryTheory AlgebraicGeometry WeierstrassProjModel
open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.DrinfeldGlobal WeierstrassCurve.Affine

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K8EQA

theorem drinVCInv (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (W : WeierstrassCurve Ω) [W.IsElliptic] (C : WeierstrassCurve.VariableChange Ω) [(C • W).IsElliptic]
    (u : RawDrinfeldPair Ω) (hu : RawDrinfeldPair.IsLevel 𝒢 q W u) (D : ModularCurve.LevelPData Ω)
    (hP : IsSectionThrough u.P D.xP D.yP) (hQ : IsSectionThrough u.Q D.xQ D.yQ) :
    weilPairing0 (C • W) Ω (q : ℤ)
        (toPoint ((C • W).baseChange Ω) (D.variableChange C).xP (D.variableChange C).yP)
        (toPoint ((C • W).baseChange Ω) (D.variableChange C).xQ (D.variableChange C).yQ) =
      weilPairing0 W Ω (q : ℤ) (toPoint (W.baseChange Ω) D.xP D.yP) (toPoint (W.baseChange Ω) D.xQ D.yQ) := by
  have hq2 : q ≠ 2 := by omega
  have hD : ModularCurve.IsLevelPStructure W q D :=
    K8EQ.isLevelPStructure_of_isSectionThrough q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hq2 W (isUnit_iff_ne_zero.mpr hqΩ) u hu D hP hQ
  exact WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange W C q hq3 hqΩ D hD

end K8EQA

namespace K8EQB

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve WeierstrassCurve.Affine

theorem exists_ext (R₀ : Type) [CommRing R₀] [IsDomain R₀] {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (ε : R₀ →+* Ω) (hε : Function.Injective ε) :
    ∃ ε' : AlgebraicClosure (FractionRing R₀) →+* Ω, ∀ r, ε' (algebraMap R₀ _ r) = ε r := by
  let εF : FractionRing R₀ →+* Ω := IsFractionRing.lift hε
  letI : Algebra (FractionRing R₀) Ω := εF.toAlgebra
  let ε' : AlgebraicClosure (FractionRing R₀) →ₐ[FractionRing R₀] Ω :=
    IsAlgClosed.lift (R := FractionRing R₀) (S := AlgebraicClosure (FractionRing R₀)) (M := Ω)
  refine ⟨ε'.toRingHom, fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply R₀ (FractionRing R₀) (AlgebraicClosure (FractionRing R₀)) r]
  show ε' (algebraMap (FractionRing R₀) _ (algebraMap R₀ (FractionRing R₀) r)) = ε r
  rw [AlgHom.commutes]
  exact IsFractionRing.lift_algebraMap hε r

theorem map_toPoint {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K']
    [DecidableEq K] [DecidableEq K']
    (W : WeierstrassCurve F) (f : K →ₐ[F] K') (x y : K) :
    WeierstrassCurve.Affine.Point.map f (toPoint (W⁄K) x y) = toPoint (W⁄K') (f x) (f y) := by
  unfold toPoint
  by_cases h : (W⁄K).toAffine.Nonsingular x y
  · have h' : (W⁄K').toAffine.Nonsingular (f x) (f y) := (WeierstrassCurve.Affine.baseChange_nonsingular W (f := f) (RingHom.injective (f : K →+* K')) x y).mpr h
    rw [dif_pos h, dif_pos h', WeierstrassCurve.Affine.Point.map_some]
  · have h' : ¬ (W⁄K').toAffine.Nonsingular (f x) (f y) := fun h' => h ((WeierstrassCurve.Affine.baseChange_nonsingular W (f := f) (RingHom.injective (f : K →+* K')) x y).mp h')
    rw [dif_neg h, dif_neg h', map_zero]

theorem side {Ω₀ Ω : Type} [Field Ω₀] [IsAlgClosed Ω₀] [DecidableEq Ω₀] [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (ε : Ω₀ →+* Ω) (W₀ : WeierstrassCurve Ω₀) [W₀.IsElliptic] (n : ℕ) (hn : (n : Ω₀) ≠ 0)
    (xP yP xQ yQ : Ω₀)
    (hS : (n : ℤ) • toPoint (W₀⁄Ω₀) xP yP = 0) (hT : (n : ℤ) • toPoint (W₀⁄Ω₀) xQ yQ = 0) :
    ((weilPairing0 (W₀.map ε) Ω (n : ℤ) (toPoint ((W₀.map ε)⁄Ω) (ε xP) (ε yP)) (toPoint ((W₀.map ε)⁄Ω) (ε xQ) (ε yQ)) : Ωˣ) : Ω)
      = ε ((weilPairing0 W₀ Ω₀ (n : ℤ) (toPoint (W₀⁄Ω₀) xP yP) (toPoint (W₀⁄Ω₀) xQ yQ) : Ω₀ˣ) : Ω₀) := by
  letI : Algebra Ω₀ Ω := ε.toAlgebra
  haveI : (W₀⁄Ω₀).IsElliptic := by dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  haveI : (W₀⁄Ω).IsElliptic := by dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  haveI : IsDedekindDomain (W₀⁄Ω₀).toAffine.CoordinateRing := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W₀⁄Ω₀)
  haveI : IsDedekindDomain (W₀⁄Ω).toAffine.CoordinateRing := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W₀⁄Ω)
  have hpres : (W₀.map ε)⁄Ω = W₀⁄Ω := by
    show (W₀.map ε).map (algebraMap Ω Ω) = W₀.map (algebraMap Ω₀ Ω)
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]; rfl
  rw [WeierstrassCurve.Affine.weilPairing0_toPoint_eq_of_baseChange_eq (W₀.map ε) W₀ hpres]
  have eP : toPoint (W₀⁄Ω) (ε xP) (ε yP) = WeierstrassCurve.Affine.Point.map (Algebra.ofId Ω₀ Ω) (toPoint (W₀⁄Ω₀) xP yP) := by
    rw [map_toPoint]; rfl
  have eQ : toPoint (W₀⁄Ω) (ε xQ) (ε yQ) = WeierstrassCurve.Affine.Point.map (Algebra.ofId Ω₀ Ω) (toPoint (W₀⁄Ω₀) xQ yQ) := by
    rw [map_toPoint]; rfl
  rw [eP, eQ, WeierstrassCurve.Affine.weilPairing0_map_algHom W₀ (Algebra.ofId Ω₀ Ω) hn _ _ hS hT]
  rfl

theorem zsmul_toPoint_eq_zero {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) {x y : F} (heq : (W⁄F).toAffine.Equation x y)
    (hpre : ((W⁄F).preΨ q).eval x = 0) : (q : ℤ) • toPoint (W⁄F) x y = 0 := by
  haveI : (W⁄F).IsElliptic := by dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hns : (W⁄F).toAffine.Nonsingular x y := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq
  have hodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  unfold toPoint
  rw [dif_pos hns, natCast_zsmul]
  rw [WeierstrassCurve.preΨ_ofNat] at hpre
  exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi (W⁄F) hodd hns).mpr hpre

end K8EQB

open K8EQA K8EQB in
theorem solution
    (A : Type) [CommRing A] (ℓg M' q : ℕ) [Fact ℓg.Prime] [NeZero M'] [Fact q.Prime] (hq3 : 3 ≤ q)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    (K : Type) [Field K] [Algebra A K] (ζ : A) (hζ : IsPrimitiveRoot (algebraMap A K ζ) q)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω]
    (x₁ x₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw K)
    (hy₁ : (Quot.mk _ y₁ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt K) = x₁)
    (hy₂ : (Quot.mk _ y₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt K) = x₂)
    (D₁ D₂ : ModularCurve.LevelPData Ω)
    (hD₁ : IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁).level.2.2.P D₁.xP D₁.yP ∧
      IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁).level.2.2.Q D₁.xQ D₁.yQ)
    (hD₂ : IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂).level.2.2.P D₂.xP D₂.yP ∧
      IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂).level.2.2.Q D₂.xQ D₂.yQ) :
    letI z₁ := (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁
    letI z₂ := (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂
    letI _ : (z₁.curve).IsElliptic := ⟨z₁.isUnit_Δ⟩
    letI _ : (z₂.curve).IsElliptic := ⟨z₂.isUnit_Δ⟩
    ((weilPairing0 z₁.curve Ω (q : ℤ)
        (toPoint ((z₁.curve).baseChange Ω) D₁.xP D₁.yP)
        (toPoint ((z₁.curve).baseChange Ω) D₁.xQ D₁.yQ) : Ωˣ) : Ω) =
      ((weilPairing0 z₂.curve Ω (q : ℤ)
        (toPoint ((z₂.curve).baseChange Ω) D₂.xP D₂.yP)
        (toPoint ((z₂.curve).baseChange Ω) D₂.xQ D₂.yQ) : Ωˣ) : Ω) := by
  classical

  obtain ⟨w, κ₁, κ₂, C₁, C₂, hκ₁, hκ₂, hκ₁v, hy₁e, hy₂e⟩ :=
    ModularCurve.LevelModuliPackageAbs.exists_eq_act_mapRing_of_ker_classify_eq A
      (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯) P₀ K x₁ x₂ h y₁ y₂ hy₁ hy₂
  subst hy₁e hy₂e

  have hz : ∀ (κ : ↥(P₀.classify x₁).range →ₐ[A] K) (C : WeierstrassCurve.VariableChange K),
      (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω)
          ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing κ w)) =
        (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act (C.map (IsScalarTower.toAlgHom A K Ω).toRingHom)
          ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((IsScalarTower.toAlgHom A K Ω).comp κ) w) := by
    intro κ C
    rw [(rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing_act, ← (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing_comp]
  generalize hm₁ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₁ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing κ₁ w)) = m₁ at hD₁ ⊢
  generalize hm₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₂ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing κ₂ w)) = m₂ at hD₂ ⊢
  rw [hz] at hm₁ hm₂
  subst hm₁ hm₂

  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqK : ((q : ℕ) : K) ≠ 0 := (hζ.neZero').out
  have hιinj : Function.Injective (IsScalarTower.toAlgHom A K Ω) := (algebraMap K Ω).injective
  have hqΩ : ((q : ℕ) : Ω) ≠ 0 := by
    intro h0; apply hqK
    have : (IsScalarTower.toAlgHom A K Ω) (q : K) = 0 := by rw [map_natCast]; exact h0
    exact (map_eq_zero_iff _ hιinj).mp this

  haveI hdom : IsDomain ↥(P₀.classify x₁).range := inferInstance
  let Ω₀ : Type := AlgebraicClosure (FractionRing ↥(P₀.classify x₁).range)
  letI : DecidableEq Ω₀ := Classical.decEq _
  haveI : IsScalarTower A ↥(P₀.classify x₁).range Ω₀ := inferInstance
  let j : ↥(P₀.classify x₁).range →ₐ[A] Ω₀ := IsScalarTower.toAlgHom A ↥(P₀.classify x₁).range Ω₀
  have hjinj : Function.Injective (algebraMap ↥(P₀.classify x₁).range Ω₀) := by
    rw [IsScalarTower.algebraMap_eq ↥(P₀.classify x₁).range (FractionRing ↥(P₀.classify x₁).range) Ω₀]
    exact (algebraMap (FractionRing ↥(P₀.classify x₁).range) Ω₀).injective.comp
      (IsFractionRing.injective ↥(P₀.classify x₁).range (FractionRing ↥(P₀.classify x₁).range))
  have hqR₀ : ((q : ℕ) : ↥(P₀.classify x₁).range) ≠ 0 := by
    intro h0; apply hqK; have := congrArg (Subtype.val) h0; simpa using this
  have hqΩ₀ : ((q : ℕ) : Ω₀) ≠ 0 := by
    intro h0; apply hqR₀
    exact (map_eq_zero_iff _ hjinj).mp (by rw [map_natCast]; exact h0)

  have hε₁ : Function.Injective ((IsScalarTower.toAlgHom A K Ω).comp κ₁) := hιinj.comp hκ₁
  have hε₂ : Function.Injective ((IsScalarTower.toAlgHom A K Ω).comp κ₂) := hιinj.comp hκ₂
  obtain ⟨e₁, he₁⟩ := K8EQB.exists_ext ↥(P₀.classify x₁).range ((IsScalarTower.toAlgHom A K Ω).comp κ₁).toRingHom hε₁
  obtain ⟨e₂, he₂⟩ := K8EQB.exists_ext ↥(P₀.classify x₁).range ((IsScalarTower.toAlgHom A K Ω).comp κ₂).toRingHom hε₂
  have hc₁ : ∀ a : A, e₁ (algebraMap A Ω₀ a) = algebraMap A Ω a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A ↥(P₀.classify x₁).range Ω₀ a, he₁]
    exact ((IsScalarTower.toAlgHom A K Ω).comp κ₁).commutes a
  have hc₂ : ∀ a : A, e₂ (algebraMap A Ω₀ a) = algebraMap A Ω a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A ↥(P₀.classify x₁).range Ω₀ a, he₂]
    exact ((IsScalarTower.toAlgHom A K Ω).comp κ₂).commutes a
  let e₁A : Ω₀ →ₐ[A] Ω := { e₁ with commutes' := hc₁ }
  let e₂A : Ω₀ →ₐ[A] Ω := { e₂ with commutes' := hc₂ }
  have hcomp₁ : e₁A.comp j = (IsScalarTower.toAlgHom A K Ω).comp κ₁ := AlgHom.ext fun r => he₁ r
  have hcomp₂ : e₂A.comp j = (IsScalarTower.toAlgHom A K Ω).comp κ₂ := AlgHom.ext fun r => he₂ r
  have hu₁ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((IsScalarTower.toAlgHom A K Ω).comp κ₁) w = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing j w) := by
    rw [← (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing_comp, hcomp₁]
  have hu₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((IsScalarTower.toAlgHom A K Ω).comp κ₂) w = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing j w) := by
    rw [← (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing_comp, hcomp₂]
  generalize hg₁ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((IsScalarTower.toAlgHom A K Ω).comp κ₁) w = g₁ at hD₁ ⊢
  generalize hg₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ((IsScalarTower.toAlgHom A K Ω).comp κ₂) w = g₂ at hD₂ ⊢
  rw [hu₁] at hg₁; rw [hu₂] at hg₂
  subst hg₁ hg₂
  generalize hC₁' : C₁.map (IsScalarTower.toAlgHom A K Ω).toRingHom = C₁' at hD₁ ⊢
  generalize hC₂' : C₂.map (IsScalarTower.toAlgHom A K Ω).toRingHom = C₂' at hD₂ ⊢
  generalize hu₀ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing j w = u₀ at hD₁ hD₂ ⊢

  have hlev₀ : RawDrinfeldPair.IsLevel 𝒢 q u₀.curve u₀.level.2.2 := u₀.isLevel.1.2.2
  obtain ⟨⟨a, b, hPa⟩, ⟨c, d, hQc⟩⟩ := RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯
    u₀.curve (isUnit_iff_ne_zero.mpr hqΩ₀) u₀.level.2.2 hlev₀
  let E₀ : ModularCurve.LevelPData Ω₀ := ⟨a, b, c, d⟩

  have hco₁ := isSectionThrough_map_of_isSectionTransport A 𝒢 q 𝒯 h𝒯 e₁A u₀.level.2.2
    (hCO _ _ e₁A u₀.level.2.2.curve) E₀ hPa hQc
  have hco₂ := isSectionThrough_map_of_isSectionTransport A 𝒢 q 𝒯 h𝒯 e₂A u₀.level.2.2
    (hCO _ _ e₂A u₀.level.2.2.curve) E₀ hPa hQc
  have hact₁ := isSectionThrough_act_of_isSectionTransport A 𝒢 q 𝒯 h𝒯 C₁' (𝒯.map e₁A u₀.level.2.2)
    (hVC _ _ C₁') (E₀.map e₁A.toRingHom) hco₁.1 hco₁.2
  have hact₂ := isSectionThrough_act_of_isSectionTransport A 𝒢 q 𝒯 h𝒯 C₂' (𝒯.map e₂A u₀.level.2.2)
    (hVC _ _ C₂') (E₀.map e₂A.toRingHom) hco₂.1 hco₂.2
  obtain ⟨hx₁P, hy₁P⟩ := K8EQ.coords_unique hD₁.1 hact₁.1
  obtain ⟨hx₁Q, hy₁Q⟩ := K8EQ.coords_unique hD₁.2 hact₁.2
  obtain ⟨hx₂P, hy₂P⟩ := K8EQ.coords_unique hD₂.1 hact₂.1
  obtain ⟨hx₂Q, hy₂Q⟩ := K8EQ.coords_unique hD₂.2 hact₂.2
  rw [hx₁P, hy₁P, hx₁Q, hy₁Q, hx₂P, hy₂P, hx₂Q, hy₂Q]

  haveI iW₁ : ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A u₀).curve.IsElliptic := ⟨((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A u₀).isUnit_Δ⟩
  haveI iW₂ : ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A u₀).curve.IsElliptic := ⟨((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A u₀).isUnit_Δ⟩
  haveI iCW₁ : (C₁' • ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A u₀).curve).IsElliptic := ⟨((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₁' ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A u₀)).isUnit_Δ⟩
  haveI iCW₂ : (C₂' • ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A u₀).curve).IsElliptic := ⟨((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C₂' ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A u₀)).isUnit_Δ⟩
  have key₁ := WeierstrassCurve.DrinfeldGlobal.weilPairing0_toPoint_variableChange_of_isLevel_of_isSectionThrough
    A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 hqΩ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A u₀).curve C₁' ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A u₀).level.2.2
    ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₁A u₀).isLevel.1.2.2 (E₀.map e₁A.toRingHom) hco₁.1 hco₁.2
  have key₂ := WeierstrassCurve.DrinfeldGlobal.weilPairing0_toPoint_variableChange_of_isLevel_of_isSectionThrough
    A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 hqΩ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A u₀).curve C₂' ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A u₀).level.2.2
    ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing e₂A u₀).isLevel.1.2.2 (E₀.map e₂A.toRingHom) hco₂.1 hco₂.2

  haveI iW₀ : u₀.curve.IsElliptic := ⟨u₀.isUnit_Δ⟩
  have hE₀ : ModularCurve.IsLevelPStructure u₀.curve q E₀ :=
    K8EQ.isLevelPStructure_of_isSectionThrough q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 (by omega) u₀.curve
      (isUnit_iff_ne_zero.mpr hqΩ₀) u₀.level.2.2 hlev₀ E₀ hPa hQc
  have hS₀ := K8EQB.zsmul_toPoint_eq_zero u₀.curve q hq3 hE₀.equation_P hE₀.preΨ_P
  have hT₀ := K8EQB.zsmul_toPoint_eq_zero u₀.curve q hq3 hE₀.equation_Q hE₀.preΨ_Q
  have side₁ := K8EQB.side e₁ u₀.curve q hqΩ₀ a b c d hS₀ hT₀
  have side₂ := K8EQB.side e₂ u₀.curve q hqΩ₀ a b c d hS₀ hT₀

  have hprim := WeierstrassCurve.DrinfeldGlobal.isPrimitiveRoot_weilPairing0_of_isLevel_of_isSectionThrough_ed2
    A 𝒢 h𝒢 h𝒢O q hq3 𝒯 h𝒯 (K₀ := Ω₀) hqΩ₀ Ω₀ u₀.curve u₀.level.2.2 hlev₀ E₀ hPa hQc
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hprim
  have hζΩ : IsPrimitiveRoot (algebraMap A Ω ζ) q := by
    rw [IsScalarTower.algebraMap_apply A K Ω]; exact hζ.map_of_injective (algebraMap K Ω).injective
  have hζ₁ : e₁ (algebraMap A Ω₀ ζ) = algebraMap A Ω ζ := e₁A.commutes ζ
  have hζ₂ : e₂ (algebraMap A Ω₀ ζ) = algebraMap A Ω ζ := e₂A.commutes ζ
  have hζ₀ : IsPrimitiveRoot (algebraMap A Ω₀ ζ) q :=
    IsPrimitiveRoot.of_map_of_injective (f := e₁) (by rw [hζ₁]; exact hζΩ) e₁.injective
  obtain ⟨k, -, hk⟩ := hζ₀.eq_pow_of_pow_eq_one hprim.pow_eq_one
  have fin₁ : e₁ (↑(weilPairing0 u₀.curve Ω₀ (↑q) (toPoint (u₀.curve⁄Ω₀) E₀.xP E₀.yP) (toPoint (u₀.curve⁄Ω₀) E₀.xQ E₀.yQ)) : Ω₀) = (algebraMap A Ω ζ) ^ k := by rw [← hk, map_pow, hζ₁]
  have fin₂ : e₂ (↑(weilPairing0 u₀.curve Ω₀ (↑q) (toPoint (u₀.curve⁄Ω₀) E₀.xP E₀.yP) (toPoint (u₀.curve⁄Ω₀) E₀.xQ E₀.yQ)) : Ω₀) = (algebraMap A Ω ζ) ^ k := by rw [← hk, map_pow, hζ₂]
  rw [← fin₂] at fin₁

  have L := (congrArg Units.val key₁).trans (side₁.trans fin₁)
  have R := (congrArg Units.val key₂).trans side₂
  exact L.trans R.symm

end
end S_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow (solution)
