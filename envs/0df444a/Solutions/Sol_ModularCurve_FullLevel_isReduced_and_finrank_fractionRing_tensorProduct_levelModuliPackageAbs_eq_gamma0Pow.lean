-- Prove2me | solution 1 for ModularCurve.FullLevel.isReduced_and_finrank_fractionRing_tensorProduct_levelModuliPackageAbs_eq_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/47fb5066-9978-5ae4-a884-c756e03c30b7

import Mathlib
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
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_FullLevel_isIntegral_adjoin_j0_levelModuliPackageAbs_of_isUnit_two_three_gamma0Pow
import Theorems.Thm_Algebra_nonempty_algHom_tensorProduct_adjoin_equiv_subtype_apply_eq
import Theorems.Thm_ModularCurve_FullLevel_snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_gamma0Pow
import Theorems.Thm_ModularCurve_FullLevel_natCard_algHom_apply_jOf_univ_eq_of_transcendental_gamma0Pow
import Theorems.Thm_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
import Theorems.Thm_Matrix_natCard_GL_fin_two_zmod_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isReduced_and_finrank_fractionRing_tensorProduct_levelModuliPackageAbs_eq_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth WeierstrassCurve.Generic.isElliptic_curve ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing"
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups TensorProduct

namespace RedRank33

theorem transcendental_rat_of_forall_aeval_eq_zero {A Ω : Type} [CommRing A] [CharZero A] [Field Ω] [CharZero Ω]
    [Algebra A Ω] (t : Ω) (h : ∀ p : Polynomial A, Polynomial.aeval t p = 0 → p = 0) : Transcendental ℚ t := by
  intro halg
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have hZ : IsAlgebraic ℤ t := (Algebra.IsAlgebraic.isAlgebraic_iff ℤ ℚ).mpr halg
  obtain ⟨p, hp0, hp⟩ := hZ
  apply hp0
  have h1 : Polynomial.aeval t (p.map (algebraMap ℤ A)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]; exact hp
  have h2 := h _ h1
  rwa [Polynomial.map_eq_zero_iff (algebraMap ℤ A).injective_int] at h2

end RedRank33

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

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
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L (q * ℓ))
    [IsDomain ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))] :
    IsReduced (TensorProduct ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀)) (FractionRing ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))) P₀.B₀) ∧
      Module.finrank (FractionRing ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))) (TensorProduct ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀)) (FractionRing ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))) P₀.B₀) =
        (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
          Nat.card (GL (Fin 2) (ZMod ℓ)) * Nat.card (GL (Fin 2) (ZMod q)) / 2 := by
  classical
  set S : Subalgebra A P₀.B₀ := Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀) with hSdef
  set ι : P₀.B₀ →ₐ[A] ↥K := P₀.classify x with hιdef
  have hj₀ : P₀.j₀ = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ := rfl

  have hy : ((ι P₀.j₀ : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) := by
    rw [← hx]; congr 1
    show ι ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) = _
    rw [← (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf_map ι P₀.univ, hιdef, P₀.map_classify]
  have hjtr : ∀ f : Polynomial A, Polynomial.aeval P₀.j₀ f = 0 → f = 0 := by
    set κ : P₀.B₀ →+* LaurentSeries L := (IntermediateField.val K).toRingHom.comp ι.toRingHom with hκ
    have hκapp : ∀ b : P₀.B₀, κ b = ((ι b : ↥K) : LaurentSeries L) := fun b => rfl
    have hκA : κ.comp (algebraMap A P₀.B₀) = (algebraMap L (LaurentSeries L)).comp (algebraMap A L) := by
      ext a
      simp only [RingHom.comp_apply, hκapp, AlgHom.commutes, IsScalarTower.algebraMap_apply A L ↥K a]
      rfl
    have hκf : ∀ f : Polynomial A, κ (Polynomial.aeval P₀.j₀ f) =
        Polynomial.aeval (κ P₀.j₀) (f.map (algebraMap A L)) := by
      intro f
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, ← hκA, ← Polynomial.hom_eval₂]
    have hT : Transcendental L (κ P₀.j₀) := by
      rw [hκapp, hy]; exact ModularCurve.transcendental_jqNModC L (q * ℓ)
    intro f hf
    have hfκ : Polynomial.aeval (κ P₀.j₀) (f.map (algebraMap A L)) = 0 := by
      rw [← hκf, hf, map_zero]
    have hf0 : f.map (algebraMap A L) = 0 := (transcendental_iff.mp hT) _ hfκ
    rwa [Polynomial.map_eq_zero_iff (IsFractionRing.injective A L)] at hf0

  have hint : Algebra.IsIntegral ↥S P₀.B₀ := by
    have hunit : ∀ n : ℕ, Nat.Coprime n q → IsUnit ((n : ℕ) : A) := by
      intro n hn
      by_contra hnu
      have hmem : ((n : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * n + b * q = 1 := by
        obtain ⟨a, b, h⟩ := Nat.Coprime.isCoprime hn; exact ⟨a, b, h⟩
      have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
        have : ((a : ℤ) : A) * ((n : ℕ) : A) + ((b : ℤ) : A) * ((q : ℕ) : A) = 1 := by
          have := congrArg (fun z : ℤ => ((z : ℤ) : A)) hab; push_cast at this; exact this
        rw [← this]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hAq)
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have h2A : IsUnit ((2 : ℕ) : A) :=
      hunit 2 (Nat.Coprime.symm ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr (by omega)))
    have h3A : IsUnit ((3 : ℕ) : A) :=
      hunit 3 (Nat.Coprime.symm ((Nat.coprime_primes (Fact.out) Nat.prime_three).mpr (by omega)))
    exact ModularCurve.FullLevel.isIntegral_adjoin_j0_levelModuliPackageAbs_of_isUnit_two_three_gamma0Pow
      A q ℓ M' hℓ3 hℓA hM'A h2A h3A hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO P₀
  haveI : Algebra.FiniteType ↥S P₀.B₀ := Algebra.FiniteType.of_restrictScalars_finiteType A ↥S P₀.B₀
  haveI : Module.Finite ↥S P₀.B₀ := Algebra.IsIntegral.finite
  haveI : Module.Finite (FractionRing ↥S) ((FractionRing ↥S) ⊗[↥S] P₀.B₀) := inferInstance

  haveI : CharZero A := RingHom.charZero (algebraMap A L)
  have hS_inj : Function.Injective (algebraMap A ↥S) := by
    intro a₁ a₂ h
    have h' : Polynomial.aeval P₀.j₀ (Polynomial.C (a₁ - a₂)) = 0 := by
      rw [Polynomial.aeval_C, map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val h)
    have := hjtr _ h'
    rwa [Polynomial.C_eq_zero, sub_eq_zero] at this
  haveI : CharZero ↥S := charZero_of_injective_algebraMap hS_inj
  haveI : CharZero (FractionRing ↥S) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective ↥S (FractionRing ↥S))
  let Ω : Type := AlgebraicClosure (FractionRing ↥S)
  haveI : CharZero Ω := charZero_of_injective_algebraMap ((algebraMap (FractionRing ↥S) Ω).injective)
  have hSΩ_inj : Function.Injective (algebraMap ↥S Ω) := by
    rw [IsScalarTower.algebraMap_eq ↥S (FractionRing ↥S) Ω]
    exact (algebraMap (FractionRing ↥S) Ω).injective.comp (IsFractionRing.injective ↥S (FractionRing ↥S))
  let j₀S : ↥S := ⟨P₀.j₀, Algebra.self_mem_adjoin_singleton A P₀.j₀⟩
  let t : Ω := algebraMap ↥S Ω j₀S
  have hqΩ : ((q : ℕ) : Ω) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have ht := RedRank33.transcendental_rat_of_forall_aeval_eq_zero (A := A) t (fun p hp => by
    have h2 : algebraMap ↥S Ω (Polynomial.aeval j₀S p) = 0 := by
      rw [← Polynomial.aeval_algebraMap_apply]; exact hp
    have h3 : Polynomial.aeval j₀S p = 0 := hSΩ_inj (by rw [h2, map_zero])
    have h4 : Polynomial.aeval P₀.j₀ p = 0 := by
      have := Polynomial.aeval_algHom_apply S.val j₀S p
      rw [h3, map_zero] at this
      exact this
    exact hjtr _ h4)

  have e1 : algebraMap ↥S ((FractionRing ↥S) ⊗[↥S] P₀.B₀) j₀S = (1 : FractionRing ↥S) ⊗ₜ[↥S] P₀.j₀ := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, ← TensorProduct.tmul_smul,
      Algebra.smul_def, mul_one]
    rfl
  have hG2 : ∀ (φ : ((FractionRing ↥S) ⊗[↥S] P₀.B₀) →ₐ[FractionRing ↥S] DualNumber Ω)
      (r : (FractionRing ↥S) ⊗[↥S] P₀.B₀), (φ r).snd = 0 := by
    intro φ
    let ψ : P₀.B₀ →ₐ[A] DualNumber Ω := ((φ.restrictScalars ↥S).comp
      (Algebra.TensorProduct.includeRight (R := ↥S) (A := FractionRing ↥S) (B := P₀.B₀))).restrictScalars A
    have hψ : ∀ b : P₀.B₀, ψ b = φ ((1 : FractionRing ↥S) ⊗ₜ[↥S] b) := fun b => rfl
    have hψj : ψ ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) =
        algebraMap Ω (DualNumber Ω) t := by
      rw [← hj₀, hψ, ← e1]
      have := (φ.restrictScalars ↥S).commutes j₀S
      rw [AlgHom.restrictScalars_apply] at this
      rw [this, IsScalarTower.algebraMap_apply ↥S Ω (DualNumber Ω)]
    have h0 := ModularCurve.FullLevel.snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_gamma0Pow
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' A hℓA hM'A hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO P₀ Ω hqΩ t ht ψ hψj
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul f b =>
        have : (f ⊗ₜ[↥S] b : (FractionRing ↥S) ⊗[↥S] P₀.B₀) = f • ((1 : FractionRing ↥S) ⊗ₜ[↥S] b) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, TrivSqZeroExt.snd_smul, ← hψ, h0 b, smul_zero]
    | add x y hx' hy' => rw [map_add, TrivSqZeroExt.snd_add, hx', hy', add_zero]

  obtain ⟨hred, hrank⟩ := Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
    (FractionRing ↥S) ((FractionRing ↥S) ⊗[↥S] P₀.B₀) Ω hG2
  obtain ⟨ebc⟩ := Algebra.nonempty_algHom_tensorProduct_adjoin_equiv_subtype_apply_eq (A := A) (B := P₀.B₀)
    P₀.j₀ (FractionRing ↥S) Ω
  have hD1 := ModularCurve.FullLevel.natCard_algHom_apply_jOf_univ_eq_of_transcendental_gamma0Pow
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' A hℓA hM'A hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO P₀ Ω hqΩ t ht
  refine ⟨hred, ?_⟩
  rw [hrank, Nat.card_congr ebc]
  exact hD1

end S_ModularCurve_FullLevel_isReduced_and_finrank_fractionRing_tensorProduct_levelModuliPackageAbs_eq_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_isReduced_and_finrank_fractionRing_tensorProduct_levelModuliPackageAbs_eq_gamma0Pow (solution)
