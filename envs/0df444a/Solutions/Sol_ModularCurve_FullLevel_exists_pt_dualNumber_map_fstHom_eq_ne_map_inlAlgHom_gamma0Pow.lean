-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_pt_dualNumber_map_fstHom_eq_ne_map_inlAlgHom_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/fa8ddf6f-9c64-5454-8f82-37a83c60e06d

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_FullLevel_exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow
import Theorems.Thm_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_pt_dualNumber_map_fstHom_eq_ne_map_inlAlgHom_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one"
p2m_attr_erase "simp" "GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (A : Type) [CommRing A]
    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (x₀ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt Ω) :
    ∃ y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt (DualNumber Ω),
      (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A) y = x₀ ∧
      y ≠ (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A) x₀ := by
  classical

  set Lf : ModularCurve.LevelComponent A :=
    (ModularCurve.gamma0PowComponent A M' hM).prod
      ((ModularCurve.levelPComponent A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯)) with hLf
  set Le : ModularCurve.LevelComponent A :=
    (ModularCurve.gamma0PowComponent A M' hM).prod
      ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A))) with hLe
  have hD : rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯 = Lf.toRigid := rfl
  set fstA : DualNumber Ω →ₐ[A] Ω := (TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A with hfstA
  set inlA : Ω →ₐ[A] DualNumber Ω := (TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A with hinlA

  let πr : ∀ (T : Type) [CommRing T] [Algebra A T], Lf.Raw T → Le.Raw T := fun T _ _ r =>
    ⟨r.curve, r.isUnit_Δ, (r.level.1, (r.level.2.1, PUnit.unit)), ⟨r.isLevel.1, ⟨r.isLevel.2.1, trivial⟩⟩⟩
  have πr_act : ∀ (T : Type) [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (r : Lf.Raw T),
      πr T (Lf.toRigid.act C r) = Le.toRigid.act C (πr T r) := by
    intro T _ _ C r; rfl
  have πr_map : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (r : Lf.Raw T),
      πr T' (Lf.toRigid.mapRing f r) = Le.toRigid.mapRing f (πr T r) := by
    intro T T' _ _ _ _ f r; rfl
  let πPt : ∀ (T : Type) [CommRing T] [Algebra A T], Lf.toRigid.Pt T → Le.toRigid.Pt T := fun T _ _ =>
    Quot.lift (fun r => Quot.mk _ (πr T r)) (by
      rintro a b ⟨C, rfl⟩
      exact Quot.sound ⟨C, πr_act T C a⟩)
  have πPt_mk : ∀ (T : Type) [CommRing T] [Algebra A T] (r : Lf.Raw T),
      πPt T (Quot.mk _ r) = Quot.mk _ (πr T r) := by
    intro T _ _ r; rfl
  have πPt_map : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (x : Lf.toRigid.Pt T), πPt T' (Lf.toRigid.map f x) = Le.toRigid.map f (πPt T x) := by
    intro T T' _ _ _ _ f x
    induction x using Quot.ind with
    | mk r => rfl

  have hℓΩ : ((ℓ : ℕ) : Ω) ≠ 0 := by
    have := hℓA.map (algebraMap A Ω); rw [map_natCast] at this; exact this.ne_zero
  have hM'Ω : ((M' : ℕ) : Ω) ≠ 0 := by
    have := hM'A.map (algebraMap A Ω); rw [map_natCast] at this; exact this.ne_zero

  induction x₀ using Quot.ind with
  | mk r =>

  obtain ⟨y₁, hy₁fst, hy₁ne, -⟩ :=
    ModularCurve.FullLevel.exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow ℓ M' hℓ3 A hℓ hM Ω hℓΩ hM'Ω
      (Quot.mk _ (πr Ω r))
  obtain ⟨s, hs⟩ := Quot.exists_rep y₁

  have hmk : (Quot.mk _ (Le.toRigid.mapRing fstA s) : Le.toRigid.Pt Ω) = Quot.mk _ (πr Ω r) := by
    rw [← ModularCurve.RigidWeierstrassData.map_mk, hs]; exact hy₁fst
  obtain ⟨C₀, hC₀⟩ := ModularCurve.RigidWeierstrassData.exists_eq_act_of_mk_eq_mk Le.toRigid _ _ hmk
  set s' : Le.Raw (DualNumber Ω) := Le.toRigid.act (C₀.map inlA.toRingHom) s with hs'
  have hC₀map : (C₀.map inlA.toRingHom).map fstA.toRingHom = C₀ := by
    rw [WeierstrassCurve.VariableChange.map_map,
      show fstA.toRingHom.comp inlA.toRingHom = RingHom.id Ω from RingHom.ext (fun x => rfl),
      WeierstrassCurve.VariableChange.map_id]
  have hs'fst : Le.toRigid.mapRing fstA s' = πr Ω r := by
    rw [hs', ModularCurve.RigidWeierstrassData.mapRing_act, hC₀map, ← hC₀]
  have hs'mk : (Quot.mk _ s' : Le.toRigid.Pt (DualNumber Ω)) = y₁ := by
    rw [← hs]; exact (Quot.sound ⟨C₀.map inlA.toRingHom, rfl⟩).symm

  have hcurve : s'.curve.map fstA.toRingHom = r.curve := congrArg ModularCurve.LevelComponent.Raw.curve hs'fst
  have hz₀ : RawDrinfeldPair.IsLevel 𝒢 q (s'.curve.map fstA.toRingHom) r.level.2.2 := by
    rw [hcurve]; exact r.isLevel.2.2
  obtain ⟨z, hzlev, hzmap⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel q (by omega) A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hCO
      Ω hqΩ s'.curve s'.isUnit_Δ r.level.2.2 hz₀

  let yraw : Lf.Raw (DualNumber Ω) :=
    ⟨s'.curve, s'.isUnit_Δ, (s'.level.1, (s'.level.2.1, z)), ⟨s'.isLevel.1, ⟨s'.isLevel.2.1, hzlev⟩⟩⟩
  refine ⟨Quot.mk _ yraw, ?_, ?_⟩
  ·
    show Lf.toRigid.map fstA (Quot.mk _ yraw) = Quot.mk _ r
    rw [ModularCurve.RigidWeierstrassData.map_mk]
    congr 1
    have hlev := congrArg ModularCurve.LevelComponent.Raw.level hs'fst
    have h1 : (ModularCurve.gamma0PowComponent A M' hM).map fstA s'.level.1 = r.level.1 := congrArg Prod.fst hlev
    have h2 : (ModularCurve.levelPComponent A ℓ hℓ).map fstA s'.level.2.1 = r.level.2.1 :=
      congrArg (fun p => p.2.1) hlev
    apply ModularCurve.LevelComponent.Raw.ext' hcurve
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact h1
    · exact h2
    · exact hzmap
  ·
    intro heq
    apply hy₁ne
    have h1 : πPt (DualNumber Ω) (Quot.mk _ yraw) = πPt (DualNumber Ω) (Lf.toRigid.map inlA (Quot.mk _ r)) :=
      congrArg (πPt (DualNumber Ω)) heq
    rw [πPt_map, πPt_mk, πPt_mk] at h1
    rw [← hs'mk]
    have hs'' : s' = πr (DualNumber Ω) yraw := ModularCurve.LevelComponent.Raw.ext' rfl rfl
    rw [hs'']
    exact h1

end S_ModularCurve_FullLevel_exists_pt_dualNumber_map_fstHom_eq_ne_map_inlAlgHom_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_pt_dualNumber_map_fstHom_eq_ne_map_inlAlgHom_gamma0Pow (solution)
