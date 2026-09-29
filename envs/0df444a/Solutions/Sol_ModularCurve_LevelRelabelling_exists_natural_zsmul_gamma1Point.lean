-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.exists_natural_zsmul_gamma1Point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/12d3f17f-e463-5ca0-b0f9-5352dfc2f272

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_zlinComb_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_act_of_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_eval_prePsi_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

p2m_open "AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.LevelRelabelling"
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.variableChange LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ LevelRelabelling.toPoint LevelRelabelling.zsmulSection IsGamma1Point"
namespace LevelRelabelling
p2m_export "ModularCurve.LevelRelabelling" "toPoint zsmulSection zlinComb RawDrinfeldPair.relabel"
namespace DiamAlg
p2m_open "ModularCurve.LevelRelabelling ModularCurve"

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))

theorem nsmul_eq_pow (n : ℕ) (x : Section W) :
    letI := G.pointGroup (𝟙 _); G.nsmul (𝟙 _) n x = x ^ n := by
  letI := G.pointGroup (𝟙 _)
  induction n with
  | zero => rfl
  | succ n ih => rw [G.nsmul_succ, ih, pow_succ]; rfl

theorem zsmulSection_eq_zpow (n : ℤ) (x : Section W) :
    letI := G.pointGroup (𝟙 _); zsmulSection G n x = x ^ n := by
  letI := G.pointGroup (𝟙 _)
  cases n with
  | ofNat k =>
    show G.nsmul (𝟙 _) k x = x ^ ((k : ℕ) : ℤ)
    rw [nsmul_eq_pow, zpow_natCast]
  | negSucc k =>
    show G.inv (𝟙 _) (G.nsmul (𝟙 _) (k + 1) x) = x ^ (Int.negSucc k)
    rw [nsmul_eq_pow, zpow_negSucc]
    rfl

theorem zlinComb_eq_zpow_mul_zpow (P Q : Section W) (a b : ℤ) :
    letI := G.pointGroup (𝟙 _); zlinComb G P Q a b = P ^ a * Q ^ b := by
  letI := G.pointGroup (𝟙 _)
  show G.mul (𝟙 _) (zsmulSection G a P) (zsmulSection G b Q) = P ^ a * Q ^ b
  rw [zsmulSection_eq_zpow, zsmulSection_eq_zpow]
  rfl

theorem zlinComb_one_zero (P Q : Section W) : zlinComb G P Q 1 0 = P := by
  letI := G.pointGroup (𝟙 _)
  rw [zlinComb_eq_zpow_mul_zpow, zpow_one, zpow_zero, mul_one]

theorem zlinComb_zero_one (P Q : Section W) : zlinComb G P Q 0 1 = Q := by
  letI := G.pointGroup (𝟙 _)
  rw [zlinComb_eq_zpow_mul_zpow, zpow_zero, zpow_one, one_mul]

theorem zlinComb_zlinComb (hcomm : ∀ x y : Section W, G.mul (𝟙 _) x y = G.mul (𝟙 _) y x)
    (P Q : Section W) (g : Matrix (Fin 2) (Fin 2) ℤ) (c d : ℤ) :
    zlinComb G (zlinComb G P Q (g 0 0) (g 1 0)) (zlinComb G P Q (g 0 1) (g 1 1)) c d =
      zlinComb G P Q (g 0 0 * c + g 0 1 * d) (g 1 0 * c + g 1 1 * d) := by
  letI : CommGroup (Section W) := { G.pointGroup (𝟙 _) with mul_comm := fun x y => hcomm x y }
  have hz : ∀ (P Q : Section W) (a b : ℤ), zlinComb G P Q a b = P ^ a * Q ^ b :=
    fun P Q a b => zlinComb_eq_zpow_mul_zpow G P Q a b
  rw [hz, hz, hz, hz, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, zpow_add, zpow_add]
  ac_rfl

theorem zlinComb_zlinComb_mul (hcomm : ∀ x y : Section W, G.mul (𝟙 _) x y = G.mul (𝟙 _) y x)
    (P Q : Section W) (g h : Matrix (Fin 2) (Fin 2) ℤ) :
    zlinComb G (zlinComb G P Q (g 0 0) (g 1 0)) (zlinComb G P Q (g 0 1) (g 1 1)) (h 0 0) (h 1 0) =
        zlinComb G P Q ((g * h) 0 0) ((g * h) 1 0) ∧
      zlinComb G (zlinComb G P Q (g 0 0) (g 1 0)) (zlinComb G P Q (g 0 1) (g 1 1)) (h 0 1) (h 1 1) =
        zlinComb G P Q ((g * h) 0 1) ((g * h) 1 1) := by
  constructor
  · rw [zlinComb_zlinComb G hcomm]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [zlinComb_zlinComb G hcomm]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem zlinComb_eq_of_nsmul_eq_one (P Q : Section W) (ℓ : ℕ)
    (hP : G.nsmul (𝟙 _) ℓ P = G.one (𝟙 _)) (hQ : G.nsmul (𝟙 _) ℓ Q = G.one (𝟙 _))
    (a b a' b' : ℤ) (ha : (ℓ : ℤ) ∣ a - a') (hb : (ℓ : ℤ) ∣ b - b') :
    zlinComb G P Q a b = zlinComb G P Q a' b' := by
  letI := G.pointGroup (𝟙 _)
  have hPℓ : P ^ (ℓ : ℤ) = 1 := by rw [zpow_natCast, ← nsmul_eq_pow]; exact hP
  have hQℓ : Q ^ (ℓ : ℤ) = 1 := by rw [zpow_natCast, ← nsmul_eq_pow]; exact hQ
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, hm⟩ := hb
  have ea : a = a' + (ℓ : ℤ) * k := by omega
  have eb : b = b' + (ℓ : ℤ) * m := by omega
  rw [zlinComb_eq_zpow_mul_zpow, zlinComb_eq_zpow_mul_zpow, ea, eb, zpow_add, zpow_add, zpow_mul, zpow_mul, hPℓ, hQℓ,
    one_zpow, one_zpow, mul_one, mul_one]

end ModularCurve.LevelRelabelling.DiamAlg

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.variableChange LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ LevelRelabelling.toPoint LevelRelabelling.zsmulSection IsGamma1Point"
namespace LevelRelabelling
p2m_export "ModularCurve.LevelRelabelling" "toPoint zsmulSection zlinComb RawDrinfeldPair.relabel"
namespace DiamAlg
p2m_open "ModularCurve.LevelRelabelling ModularCurve"

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))

theorem zlinComb_self_zero (S : Section W) (a : ℤ) : zlinComb G S S a 0 = zsmulSection G a S := by
  letI := G.pointGroup (𝟙 _)
  rw [zlinComb_eq_zpow_mul_zpow, zsmulSection_eq_zpow, zpow_zero, mul_one]

theorem zsmulSection_zsmulSection (S : Section W) (a b : ℤ) :
    zsmulSection G b (zsmulSection G a S) = zsmulSection G (a * b) S := by
  letI := G.pointGroup (𝟙 _)
  rw [zsmulSection_eq_zpow, zsmulSection_eq_zpow, zsmulSection_eq_zpow, zpow_mul]

theorem zsmulSection_one (S : Section W) : zsmulSection G 1 S = S := by
  letI := G.pointGroup (𝟙 _)
  rw [zsmulSection_eq_zpow, zpow_one]

theorem zsmulSection_eq_of_nsmul_eq_one (S : Section W) (ℓ : ℕ) (hℓ : G.nsmul (𝟙 _) ℓ S = G.one (𝟙 _))
    (a a' : ℤ) (h : (a : ZMod ℓ) = (a' : ZMod ℓ)) : zsmulSection G a S = zsmulSection G a' S := by
  letI := G.pointGroup (𝟙 _)
  have hS : S ^ (ℓ : ℤ) = 1 := by rw [zpow_natCast, ← nsmul_eq_pow]; exact hℓ
  rw [zsmulSection_eq_zpow, zsmulSection_eq_zpow]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a' a ℓ).mp h.symm
  have : a = a' + ℓ * k := by linarith
  rw [this, zpow_add, zpow_mul, hS, one_zpow, mul_one]

theorem zsmulSection_eq_of_one_eq [W.toAffine.IsElliptic] (G₀ G₁ : RelativeGroupLaw T (projModelStrCR W))
    (h1 : (G₀.one (𝟙 _)).1 = (G₁.one (𝟙 _)).1) (n : ℤ) (S : Section W) :
    zsmulSection G₀ n S = zsmulSection G₁ n S := by
  have hmul : ∀ x y : Section W, G₀.mul (𝟙 _) x y = G₁.mul (𝟙 _) x y :=
    fun x y => WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic W G₀ G₁ h1 (𝟙 _) x y
  have hone : G₀.one (𝟙 _) = G₁.one (𝟙 _) := Subtype.ext h1
  have hinv : ∀ x : Section W, G₀.inv (𝟙 _) x = G₁.inv (𝟙 _) x := by
    intro x
    have A1 : G₀.mul (𝟙 _) (G₀.inv (𝟙 _) x) x = G₀.one (𝟙 _) := by
      letI := G₀.pointGroup (𝟙 _); exact inv_mul_cancel x
    have A2 : ∀ p q r : Section W, G₀.mul (𝟙 _) (G₀.mul (𝟙 _) p q) r = G₀.mul (𝟙 _) p (G₀.mul (𝟙 _) q r) := by
      letI := G₀.pointGroup (𝟙 _); exact fun p q r => mul_assoc p q r
    have A3 : ∀ p : Section W, G₀.mul (𝟙 _) p (G₀.one (𝟙 _)) = p := by
      letI := G₀.pointGroup (𝟙 _); exact fun p => mul_one p
    have A4 : ∀ p : Section W, G₀.mul (𝟙 _) (G₀.one (𝟙 _)) p = p := by
      letI := G₀.pointGroup (𝟙 _); exact fun p => one_mul p
    have B1 : G₁.mul (𝟙 _) x (G₁.inv (𝟙 _) x) = G₁.one (𝟙 _) := by
      letI := G₁.pointGroup (𝟙 _); exact mul_inv_cancel x
    calc G₀.inv (𝟙 _) x = G₀.mul (𝟙 _) (G₀.inv (𝟙 _) x) (G₀.one (𝟙 _)) := (A3 _).symm
      _ = G₀.mul (𝟙 _) (G₀.inv (𝟙 _) x) (G₀.mul (𝟙 _) x (G₁.inv (𝟙 _) x)) := by rw [hone, ← B1, hmul x]
      _ = G₁.inv (𝟙 _) x := by rw [← A2, A1, A4]
  have hns : ∀ k : ℕ, G₀.nsmul (𝟙 _) k S = G₁.nsmul (𝟙 _) k S := by
    intro k
    induction k with
    | zero => exact hone
    | succ k ih => rw [G₀.nsmul_succ, G₁.nsmul_succ, ih, hmul]
  cases n with
  | ofNat k => exact hns k
  | negSucc k =>
    show G₀.inv (𝟙 _) (G₀.nsmul (𝟙 _) (k + 1) S) = G₁.inv (𝟙 _) (G₁.nsmul (𝟙 _) (k + 1) S)
    rw [hns, hinv]

end ModularCurve.LevelRelabelling.DiamAlg

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.variableChange LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ LevelRelabelling.toPoint LevelRelabelling.zsmulSection IsGamma1Point"
namespace DiamRing
p2m_open "ModularCurve"

variable (A : Type) [CommRing A] (ℓ : ℕ)

theorem repData : ∃ (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 ℓ),
    𝒢.IsChordTangent ∧ 𝒢.IsOriginIdentity ∧ 𝒯.IsSectionTransport ∧
    (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ) ∧
    (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :=
  WeierstrassCurve.DrinfeldGlobal.exists_groupLaws_levelTransport_isChordTangent_isOriginIdentity_isSectionTransport A ℓ

def 𝒢 : GroupLaws A := (repData A ℓ).choose
def 𝒯 : LevelTransport A (𝒢 A ℓ) ℓ := (repData A ℓ).choose_spec.choose
theorem h𝒢 : (𝒢 A ℓ).IsChordTangent := (repData A ℓ).choose_spec.choose_spec.1
theorem h𝒢O : (𝒢 A ℓ).IsOriginIdentity := (repData A ℓ).choose_spec.choose_spec.2.1
theorem h𝒯 : (𝒯 A ℓ).IsSectionTransport := (repData A ℓ).choose_spec.choose_spec.2.2.1
include ℓ in
theorem hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ := (repData A ℓ).choose_spec.choose_spec.2.2.2.1
include ℓ in
theorem hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ := (repData A ℓ).choose_spec.choose_spec.2.2.2.2

variable {A ℓ}
variable {T : Type} [CommRing T] [Algebra A T]

def secThrough (W : WeierstrassCurve.Projective T) (x y : T) (h : W.toAffine.Equation x y) : Section W :=
  (((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mp h).choose

theorem secThrough_spec (W : WeierstrassCurve.Projective T) (x y : T) (h : W.toAffine.Equation x y) :
    IsSectionThrough (secThrough W x y h) x y :=
  (((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mp h).choose_spec

theorem eq_secThrough {W : WeierstrassCurve.Projective T} {x y : T} (h : W.toAffine.Equation x y) {S : Section W}
    (hS : IsSectionThrough S x y) : S = secThrough W x y h :=
  ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).2 S _ x y x y
    hS (secThrough_spec W x y h)).mpr ⟨rfl, rfl⟩

theorem coords_unique {W : WeierstrassCurve.Projective T} {S : Section W} {x y x' y' : T}
    (h : IsSectionThrough S x y) (h' : IsSectionThrough S x' y') : x = x' ∧ y = y' :=
  ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).2 S S x y x' y'
    h h').mp rfl

theorem equation_of_through {W : WeierstrassCurve.Projective T} {S : Section W} {x y : T}
    (h : IsSectionThrough S x y) : W.toAffine.Equation x y :=
  ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough W).1 x y).mpr ⟨S, h⟩

def pairOf (ℓ : ℕ) (W : WeierstrassCurve.Projective T) (D : ModularCurve.LevelPData T)
    (hD : ModularCurve.IsGamma1Point W ℓ D) : RawDrinfeldPair T :=
  ⟨W, secThrough W D.xP D.yP hD.equation_P, secThrough W D.xP D.yP hD.equation_P⟩

def M (a : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, a; 0, 0]

@[scoped simp] theorem M00 (a : ℤ) : M a 0 0 = a := rfl
@[scoped simp] theorem M10 (a : ℤ) : M a 1 0 = 0 := rfl
@[scoped simp] theorem M01 (a : ℤ) : M a 0 1 = a := rfl
@[scoped simp] theorem M11 (a : ℤ) : M a 1 1 = 0 := rfl

def Guard (ℓ : ℕ) (W : WeierstrassCurve.Projective T) (a : ℤ) (D : ModularCurve.LevelPData T) : Prop :=
  IsUnit W.Δ ∧ ModularCurve.IsGamma1Point W ℓ D ∧ ¬ ((ℓ : ℤ) ∣ a)

def coordsOf {W : WeierstrassCurve.Projective T} (S : Section W) (h : ∃ a b : T, IsSectionThrough S a b) : T × T :=
  (h.choose, h.choose_spec.choose)

theorem coordsOf_spec {W : WeierstrassCurve.Projective T} (S : Section W) (h : ∃ a b : T, IsSectionThrough S a b) :
    IsSectionThrough S (coordsOf S h).1 (coordsOf S h).2 := h.choose_spec.choose_spec

def relPair (A : Type) [CommRing A] (ℓ : ℕ) [Algebra A T] (W : WeierstrassCurve.Projective T) (a : ℤ)
    (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) : RawDrinfeldPair T :=
  RawDrinfeldPair.relabel (𝒢 A ℓ) (M a) (pairOf ℓ W D h.2.1) h.1

theorem relPair_P (A : Type) [CommRing A] (ℓ : ℕ) [Algebra A T] (W : WeierstrassCurve.Projective T) (a : ℤ)
    (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) :
    (relPair A ℓ W a D h).P = zsmulSection (𝒢 A ℓ T W h.1) a (secThrough W D.xP D.yP h.2.1.equation_P) := by
  show zlinComb (𝒢 A ℓ T W h.1) (secThrough W D.xP D.yP h.2.1.equation_P) (secThrough W D.xP D.yP h.2.1.equation_P)
    (M a 0 0) (M a 1 0) = _
  rw [M00, M10, DiamAlg.zlinComb_self_zero]

theorem relPair_Q (A : Type) [CommRing A] (ℓ : ℕ) [Algebra A T] (W : WeierstrassCurve.Projective T) (a : ℤ)
    (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) :
    (relPair A ℓ W a D h).Q = (relPair A ℓ W a D h).P := by
  show zlinComb (𝒢 A ℓ T W h.1) _ _ (M a 0 1) (M a 1 1) = zlinComb (𝒢 A ℓ T W h.1) _ _ (M a 0 0) (M a 1 0)
  rw [M00, M10, M01, M11]

theorem relPair_through (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    [Algebra A T] (W : WeierstrassCurve.Projective T) (a : ℤ) (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) :
    ∃ x y : T, IsSectionThrough (relPair A ℓ W a D h).P x y := by
  have hℓT : IsUnit ((ℓ : ℕ) : T) := by simpa using hℓA.map (algebraMap A T)
  rw [relPair_P]
  exact WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero (𝒢 A ℓ) (h𝒢 A ℓ) (h𝒢O A ℓ)
    ℓ hℓ3 T hℓT W h.1 _ D.xP D.yP (secThrough_spec W _ _ h.2.1.equation_P) h.2.1.preΨ_P a h.2.2

variable (A ℓ) in

def diam [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (a : ℤ)
    (D : ModularCurve.LevelPData T) : ModularCurve.LevelPData T :=
  if h : Guard ℓ W a D then
    ⟨(coordsOf _ (relPair_through A ℓ hℓ3 hℓA W a D h)).1, (coordsOf _ (relPair_through A ℓ hℓ3 hℓA W a D h)).2,
     (coordsOf _ (relPair_through A ℓ hℓ3 hℓA W a D h)).1, (coordsOf _ (relPair_through A ℓ hℓ3 hℓA W a D h)).2⟩
  else D

theorem diam_xQ [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (a : ℤ) (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) :
    (diam A ℓ hℓ3 hℓA T W a D).xQ = (diam A ℓ hℓ3 hℓA T W a D).xP ∧ (diam A ℓ hℓ3 hℓA T W a D).yQ = (diam A ℓ hℓ3 hℓA T W a D).yP := by
  unfold diam; rw [dif_pos h]; exact ⟨rfl, rfl⟩

theorem diam_spec [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (a : ℤ) (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) :
    IsSectionThrough (relPair A ℓ W a D h).P (diam A ℓ hℓ3 hℓA T W a D).xP (diam A ℓ hℓ3 hℓA T W a D).yP := by
  unfold diam; rw [dif_pos h]
  exact coordsOf_spec _ _

theorem diam_eq [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (a : ℤ) (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D)
    (x y : T) (hP : IsSectionThrough (relPair A ℓ W a D h).P x y) :
    diam A ℓ hℓ3 hℓA T W a D = ⟨x, y, x, y⟩ := by
  obtain ⟨e1, e2⟩ := coords_unique (diam_spec (A := A) hℓ3 hℓA W a D h) hP
  obtain ⟨e3, e4⟩ := diam_xQ (A := A) hℓ3 hℓA W a D h
  calc diam A ℓ hℓ3 hℓA T W a D
      = ⟨(diam A ℓ hℓ3 hℓA T W a D).xP, (diam A ℓ hℓ3 hℓA T W a D).yP, (diam A ℓ hℓ3 hℓA T W a D).xQ,
          (diam A ℓ hℓ3 hℓA T W a D).yQ⟩ := rfl
    _ = ⟨x, y, x, y⟩ := by rw [e3, e4, e1, e2]

theorem pairOf_eq {ℓ : ℕ} {c : WeierstrassCurve.Projective T} (r : RawDrinfeldPair T) (hc : r.curve = c)
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point c ℓ D)
    (hP : IsSectionThrough r.P D.xP D.yP) (hQ : IsSectionThrough r.Q D.xP D.yP) : pairOf ℓ c D hD = r := by
  obtain ⟨c', P', Q'⟩ := r
  dsimp only at hc hP hQ
  subst hc
  obtain rfl := eq_secThrough hD.equation_P hP
  obtain rfl := eq_secThrough hD.equation_P hQ
  rfl

theorem relabel_congr (𝒢' : GroupLaws A) (g : Matrix (Fin 2) (Fin 2) ℤ) {x y : RawDrinfeldPair T} (e : x = y)
    (hx : IsUnit x.curve.Δ) (hy : IsUnit y.curve.Δ) :
    RawDrinfeldPair.relabel 𝒢' g x hx = RawDrinfeldPair.relabel 𝒢' g y hy := by
  subst e; rfl

def dup (D : ModularCurve.LevelPData T) : ModularCurve.LevelPData T := ⟨D.xP, D.yP, D.xP, D.yP⟩

theorem relPair_map [Fact ℓ.Prime] {T' : Type} [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (a : ℤ) (D : ModularCurve.LevelPData T)
    (h : Guard ℓ W a D) (h' : Guard ℓ (W.map f.toRingHom) a (D.map f.toRingHom)) :
    relPair A ℓ (W.map f.toRingHom) a (D.map f.toRingHom) h' = (𝒯 A ℓ).map f (relPair A ℓ W a D h) := by
  obtain ⟨hc, -⟩ := (h𝒯 A ℓ).2 T T' f (pairOf ℓ W D h.2.1)
  obtain ⟨tP, tQ⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport A (𝒢 A ℓ) ℓ (𝒯 A ℓ)
    (h𝒯 A ℓ) f (pairOf ℓ W D h.2.1) (hCO A ℓ T T' f _) (dup D) (secThrough_spec _ _ _ h.2.1.equation_P)
    (secThrough_spec _ _ _ h.2.1.equation_P)
  have e1 : pairOf ℓ (W.map f.toRingHom : WeierstrassCurve.Projective T') (D.map f.toRingHom) h'.2.1 =
      (𝒯 A ℓ).map f (pairOf ℓ W D h.2.1) :=
    pairOf_eq _ hc _ h'.2.1 tP tQ
  have hΔ'' : IsUnit ((𝒯 A ℓ).map f (pairOf ℓ W D h.2.1)).curve.Δ := by rw [← e1]; exact h'.1
  unfold relPair
  rw [WeierstrassCurve.DrinfeldGlobal.LevelTransport.map_relabel_eq_relabel_map (𝒢 A ℓ) (h𝒢 A ℓ) (h𝒢O A ℓ) ℓ (𝒯 A ℓ)
    (h𝒯 A ℓ) (hVC A ℓ) (hCO A ℓ) T T' f (M a) (pairOf ℓ W D h.2.1) h.1 hΔ'']
  exact relabel_congr _ _ e1 _ _

theorem relPair_act [Fact ℓ.Prime] (C : WeierstrassCurve.VariableChange T)
    (W : WeierstrassCurve T) (a : ℤ) (D : ModularCurve.LevelPData T)
    (h : Guard ℓ W a D) (h' : Guard ℓ (C • W) a (D.variableChange C)) :
    relPair A ℓ (C • W) a (D.variableChange C) h' = (𝒯 A ℓ).act C (relPair A ℓ W a D h) := by
  obtain ⟨hc, -⟩ := (h𝒯 A ℓ).1 T C (pairOf ℓ W D h.2.1)
  obtain ⟨tP, tQ⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_act_of_isSectionTransport A (𝒢 A ℓ) ℓ (𝒯 A ℓ)
    (h𝒯 A ℓ) C (pairOf ℓ W D h.2.1) (hVC A ℓ T _ C) (dup D) (secThrough_spec _ _ _ h.2.1.equation_P)
    (secThrough_spec _ _ _ h.2.1.equation_P)
  have e1 : pairOf ℓ (C • W : WeierstrassCurve.Projective T) (D.variableChange C) h'.2.1 =
      (𝒯 A ℓ).act C (pairOf ℓ W D h.2.1) :=
    pairOf_eq _ hc _ h'.2.1 tP tQ
  have hΔ'' : IsUnit ((𝒯 A ℓ).act C (pairOf ℓ W D h.2.1)).curve.Δ := by rw [← e1]; exact h'.1
  unfold relPair
  rw [WeierstrassCurve.DrinfeldGlobal.LevelTransport.act_relabel_eq_relabel_act (𝒢 A ℓ) (h𝒢 A ℓ) (h𝒢O A ℓ) ℓ (𝒯 A ℓ)
    (h𝒯 A ℓ) (hVC A ℓ) (hCO A ℓ) T C (M a) (pairOf ℓ W D h.2.1) h.1 hΔ'']
  exact relabel_congr _ _ e1 _ _

end ModularCurve.DiamRing
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.variableChange LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ LevelRelabelling.toPoint LevelRelabelling.zsmulSection IsGamma1Point"
namespace LevelRelabelling
p2m_export "ModularCurve.LevelRelabelling" "toPoint zsmulSection zlinComb RawDrinfeldPair.relabel"
namespace DiamAlg
p2m_open "ModularCurve.LevelRelabelling ModularCurve"

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))

theorem nsmul_zsmulSection_eq_one (S : Section W) (ℓ : ℕ) (hS : G.nsmul (𝟙 _) ℓ S = G.one (𝟙 _)) (a : ℤ) :
    G.nsmul (𝟙 _) ℓ (zsmulSection G a S) = G.one (𝟙 _) := by
  letI := G.pointGroup (𝟙 _)
  have hS' : S ^ (ℓ : ℤ) = 1 := by rw [zpow_natCast, ← nsmul_eq_pow]; exact hS
  rw [nsmul_eq_pow, zsmulSection_eq_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hS', one_zpow]
  rfl

end ModularCurve.LevelRelabelling.DiamAlg
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.variableChange LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ LevelRelabelling.toPoint LevelRelabelling.zsmulSection IsGamma1Point"
p2m_open "ModularCurve"

namespace IsGamma1Point p2m_export "ModularCurve.IsGamma1Point" "map xQ_eq yQ_eq preΨ_P equation_P" end IsGamma1Point
namespace IsGamma1Point
p2m_open_scoped "ModularCurve.IsGamma1Point" in

private theorem _root_.ModularCurve.IsGamma1Point.variableChange' {T : Type u} [CommRing T] {W : WeierstrassCurve T} {ℓ : ℕ} {D : LevelPData T}
    (hD : IsGamma1Point W ℓ D) (C : WeierstrassCurve.VariableChange T) :
    IsGamma1Point (C • W) ℓ (D.variableChange C) where
  equation_P := by
    have h := hD.equation_P
    rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
    simp only [LevelPData.variableChange_xP, LevelPData.variableChange_yP, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
    linear_combination (((C.u⁻¹ : Tˣ) : T)) ^ 6 * h
  preΨ_P := by
    rw [LevelPData.variableChange_xP, WeierstrassCurve.eval_prePsi_variableChange, hD.preΨ_P, mul_zero]
  xQ_eq := by rw [LevelPData.variableChange_xQ, LevelPData.variableChange_xP, hD.xQ_eq]
  yQ_eq := by rw [LevelPData.variableChange_yQ, LevelPData.variableChange_yP, hD.yQ_eq, hD.xQ_eq]

end IsGamma1Point
p2m_export "ModularCurve" "IsGamma1Point.variableChange'"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.variableChange LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ LevelRelabelling.toPoint LevelRelabelling.zsmulSection IsGamma1Point"
namespace DiamRing
p2m_open "ModularCurve"

variable {A : Type} [CommRing A] {ℓ : ℕ}
variable {T : Type} [CommRing T] [Algebra A T]

theorem nsmul_secThrough_eq_one [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (a : ℤ) (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) :
    (𝒢 A ℓ T W h.1).nsmul (𝟙 _) ℓ (secThrough W D.xP D.yP h.2.1.equation_P) = (𝒢 A ℓ T W h.1).one (𝟙 _) := by
  have hℓT : IsUnit ((ℓ : ℕ) : T) := by simpa using hℓA.map (algebraMap A T)
  have hℓ2 : ℓ ≠ 2 := by omega
  exact (WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough (𝒢 A ℓ) (h𝒢 A ℓ)
    (h𝒢O A ℓ) ℓ hℓ2 T hℓT W h.1 _ D.xP D.yP (secThrough_spec W _ _ h.2.1.equation_P)).mpr h.2.1.preΨ_P

theorem isGamma1Point_diam [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (a : ℤ) (D : ModularCurve.LevelPData T) (h : Guard ℓ W a D) :
    ModularCurve.IsGamma1Point W ℓ (diam A ℓ hℓ3 hℓA T W a D) := by
  have hℓT : IsUnit ((ℓ : ℕ) : T) := by simpa using hℓA.map (algebraMap A T)
  have hℓ2 : ℓ ≠ 2 := by omega
  have hsp := diam_spec (A := A) hℓ3 hℓA W a D h
  obtain ⟨e3, e4⟩ := diam_xQ (A := A) hℓ3 hℓA W a D h
  refine ⟨equation_of_through hsp, ?_, e3, e4⟩
  refine (WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough (𝒢 A ℓ) (h𝒢 A ℓ)
    (h𝒢O A ℓ) ℓ hℓ2 T hℓT W h.1 _ _ _ hsp).mp ?_
  rw [relPair_P]
  exact DiamAlg.nsmul_zsmulSection_eq_one _ _ ℓ (nsmul_secThrough_eq_one (A := A) hℓ3 hℓA W a D h) a

theorem diam_map [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) {T' : Type} [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    diam A ℓ hℓ3 hℓA T' (W.map f.toRingHom) a (D.map f.toRingHom) = (diam A ℓ hℓ3 hℓA T W a D).map f.toRingHom := by
  have h : Guard ℓ W a D := ⟨hΔ, hD, ha⟩
  have hΔ' : IsUnit (W.map f.toRingHom).Δ := by rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  have h' : Guard ℓ (W.map f.toRingHom) a (D.map f.toRingHom) := ⟨hΔ', hD.map _, ha⟩
  have sP := diam_spec (A := A) hℓ3 hℓA W a D h
  have sQ : IsSectionThrough (relPair A ℓ W a D h).Q (diam A ℓ hℓ3 hℓA T W a D).xQ (diam A ℓ hℓ3 hℓA T W a D).yQ := by
    obtain ⟨e3, e4⟩ := diam_xQ (A := A) hℓ3 hℓA W a D h
    rw [relPair_Q, e3, e4]; exact sP
  obtain ⟨uP, -⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport A (𝒢 A ℓ) ℓ (𝒯 A ℓ)
    (h𝒯 A ℓ) f (relPair A ℓ W a D h) (hCO A ℓ T T' f _) (diam A ℓ hℓ3 hℓA T W a D) sP sQ
  rw [diam_eq (A := A) hℓ3 hℓA (W.map f.toRingHom) a (D.map f.toRingHom) h' _ _ (by rw [relPair_map (A := A) f W a D h h']; exact uP)]
  obtain ⟨e3, e4⟩ := diam_xQ (A := A) hℓ3 hℓA W a D h
  ext <;> simp [e3, e4]

theorem diam_variableChange [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (C : WeierstrassCurve.VariableChange T) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    diam A ℓ hℓ3 hℓA T (C • W) a (D.variableChange C) = (diam A ℓ hℓ3 hℓA T W a D).variableChange C := by
  have h : Guard ℓ W a D := ⟨hΔ, hD, ha⟩
  have hΔ' : IsUnit (C • W).Δ := by
    rw [WeierstrassCurve.variableChange_Δ]; exact ((C.u⁻¹).isUnit.pow 12).mul hΔ
  have h' : Guard ℓ (C • W) a (D.variableChange C) := ⟨hΔ', hD.variableChange' C, ha⟩
  have sP := diam_spec (A := A) hℓ3 hℓA W a D h
  have sQ : IsSectionThrough (relPair A ℓ W a D h).Q (diam A ℓ hℓ3 hℓA T W a D).xQ (diam A ℓ hℓ3 hℓA T W a D).yQ := by
    obtain ⟨e3, e4⟩ := diam_xQ (A := A) hℓ3 hℓA W a D h
    rw [relPair_Q, e3, e4]; exact sP
  obtain ⟨uP, -⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_act_of_isSectionTransport A (𝒢 A ℓ) ℓ (𝒯 A ℓ)
    (h𝒯 A ℓ) C (relPair A ℓ W a D h) (hVC A ℓ T _ C) (diam A ℓ hℓ3 hℓA T W a D) sP sQ
  rw [diam_eq (A := A) hℓ3 hℓA (C • W) a (D.variableChange C) h' _ _ (by rw [relPair_act (A := A) C W a D h h']; exact uP)]
  obtain ⟨e3, e4⟩ := diam_xQ (A := A) hℓ3 hℓA W a D h
  ext <;> simp [LevelPData.variableChange, e3, e4]

theorem diam_congr [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a a' : ℤ) (haa' : (a : ZMod ℓ) = (a' : ZMod ℓ))
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    diam A ℓ hℓ3 hℓA T W a D = diam A ℓ hℓ3 hℓA T W a' D := by
  by_cases ha : (ℓ : ℤ) ∣ a
  · have ha' : (ℓ : ℤ) ∣ a' := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at ha ⊢; rw [← haa']; exact ha
    unfold diam
    rw [dif_neg (fun h : Guard ℓ W a D => h.2.2 ha), dif_neg (fun h : Guard ℓ W a' D => h.2.2 ha')]
  · have ha' : ¬ ((ℓ : ℤ) ∣ a') := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at ha ⊢; rw [← haa']; exact ha
    have h : Guard ℓ W a D := ⟨hΔ, hD, ha⟩
    have h' : Guard ℓ W a' D := ⟨hΔ, hD, ha'⟩
    have sP' := diam_spec (A := A) hℓ3 hℓA W a' D h'
    rw [relPair_P] at sP'
    rw [diam_eq (A := A) hℓ3 hℓA W a' D h' _ _ (by rw [relPair_P]; exact sP')]
    apply diam_eq (A := A) hℓ3 hℓA W a D h
    rw [relPair_P, DiamAlg.zsmulSection_eq_of_nsmul_eq_one _ _ ℓ (nsmul_secThrough_eq_one (A := A) hℓ3 hℓA W a D h) a a' haa']
    exact sP'

theorem diam_one [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    diam A ℓ hℓ3 hℓA T W 1 D = D := by
  have h1 : ¬ ((ℓ : ℤ) ∣ 1) := by
    intro hd; have := Int.eq_one_of_dvd_one (by positivity) hd; omega
  have h : Guard ℓ W 1 D := ⟨hΔ, hD, h1⟩
  rw [diam_eq (A := A) hℓ3 hℓA W 1 D h D.xP D.yP (by rw [relPair_P, DiamAlg.zsmulSection_one]; exact secThrough_spec W _ _ hD.equation_P)]
  ext
  · rfl
  · rfl
  · exact hD.xQ_eq.symm
  · exact hD.yQ_eq.symm

theorem diam_mul [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a b : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a)) (hb : ¬ ((ℓ : ℤ) ∣ b))
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    diam A ℓ hℓ3 hℓA T W b (diam A ℓ hℓ3 hℓA T W a D) = diam A ℓ hℓ3 hℓA T W (a * b) D := by
  have hp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hab : ¬ ((ℓ : ℤ) ∣ a * b) := fun h => (hp.dvd_or_dvd h).elim ha hb
  have h : Guard ℓ W a D := ⟨hΔ, hD, ha⟩
  have hD₁ := isGamma1Point_diam (A := A) hℓ3 hℓA W a D h
  have h₁ : Guard ℓ W b (diam A ℓ hℓ3 hℓA T W a D) := ⟨hΔ, hD₁, hb⟩
  have h₂ : Guard ℓ W (a * b) D := ⟨hΔ, hD, hab⟩

  have s1 := diam_spec (A := A) hℓ3 hℓA W a D h
  rw [relPair_P] at s1
  have eS : secThrough (W : WeierstrassCurve.Projective T) _ _ hD₁.equation_P =
      zsmulSection (𝒢 A ℓ T W hΔ) a (secThrough (W : WeierstrassCurve.Projective T) D.xP D.yP hD.equation_P) :=
    (eq_secThrough _ s1).symm
  have s2 := diam_spec (A := A) hℓ3 hℓA W (a * b) D h₂
  rw [relPair_P] at s2
  rw [diam_eq (A := A) hℓ3 hℓA W (a * b) D h₂ _ _ (by rw [relPair_P]; exact s2)]
  apply diam_eq (A := A) hℓ3 hℓA W b _ h₁
  rw [relPair_P, eS, DiamAlg.zsmulSection_zsmulSection]
  exact s2

theorem through_zsmulSection [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (𝒢' : GroupLaws A) (h𝒢'O : 𝒢'.IsOriginIdentity)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D)
    (S : Section (W : WeierstrassCurve.Projective T)) (hS : IsSectionThrough S D.xP D.yP) :
    IsSectionThrough (zsmulSection (𝒢' T W hΔ) a S) (diam A ℓ hℓ3 hℓA T W a D).xP (diam A ℓ hℓ3 hℓA T W a D).yP := by
  have h : Guard ℓ W a D := ⟨hΔ, hD, ha⟩
  have s1 := diam_spec (A := A) hℓ3 hℓA W a D h
  rw [relPair_P, ← eq_secThrough hD.equation_P hS] at s1
  haveI : (W : WeierstrassCurve.Projective T).toAffine.IsElliptic := ⟨hΔ⟩
  have e1 := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢' T W hΔ)).mp
    (h𝒢'O T W hΔ)
  have e0 := (WeierstrassProjModel.RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 A ℓ T W hΔ)).mp
    (h𝒢O A ℓ T W hΔ)
  rw [DiamAlg.zsmulSection_eq_of_one_eq (𝒢' T W hΔ) (𝒢 A ℓ T W hΔ) (e1.trans e0.symm) a S]
  exact s1

section FieldCase

variable {F : Type} [Field F] [DecidableEq F]

theorem toPoint_diam [Algebra A F] [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (D : ModularCurve.LevelPData F) (hD : ModularCurve.IsGamma1Point W ℓ D) :
    toPoint W (diam A ℓ hℓ3 hℓA F W a D).xP (diam A ℓ hℓ3 hℓA F W a D).yP = a • toPoint W D.xP D.yP := by
  obtain rfl : (‹DecidableEq F›) = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨hΔ⟩
  have h : Guard ℓ W a D := ⟨hΔ, hD, ha⟩
  have nP := W.toAffine.equation_iff_nonsingular.mp hD.equation_P
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some _ _ nP with hPdef
  have hℓP : (ℓ : ℤ) • P = 0 := by
    rw [natCast_zsmul, hPdef]
    refine (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nP).mpr ?_
    rw [← WeierstrassCurve.preΨ_ofNat]; exact hD.preΨ_P
  have hP0 : P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hp
  have haP : a • P ≠ 0 := by
    intro hm
    apply ha
    by_contra hdvd
    have hcopN : Nat.Coprime ℓ a.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h0 => hdvd (Int.natCast_dvd.mpr h0))
    have hcop : IsCoprime (ℓ : ℤ) a := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact hcopN
    obtain ⟨u, v, huv⟩ := hcop
    apply hP0
    calc P = (1 : ℤ) • P := (one_zsmul P).symm
      _ = (u * ℓ + v * a) • P := by rw [huv]
      _ = u • ((ℓ : ℤ) • P) + v • (a • P) := by rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hℓP, hm, zsmul_zero, zsmul_zero, add_zero]
  obtain ⟨x', y', n', e'⟩ : ∃ (x' y' : F) (n' : W.toAffine.Nonsingular x' y'),
      a • P = WeierstrassCurve.Affine.Point.some x' y' n' := by
    cases hQ : a • P with
    | zero => exact absurd hQ haP
    | some x' y' n' => exact ⟨x', y', n', rfl⟩
  have htoP : toPoint W D.xP D.yP = P := dif_pos nP
  have e'' : a • toPoint W D.xP D.yP + (0 : ℤ) • toPoint W D.xP D.yP = WeierstrassCurve.Affine.Point.some x' y' n' := by
    rw [htoP, zero_zsmul, add_zero, e']
  obtain ⟨-, t⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_zlinComb_of_isSectionThrough A (𝒢 A ℓ) (h𝒢 A ℓ)
    (h𝒢O A ℓ) (W : WeierstrassCurve.Projective F) hΔ _ _ _ _ _ _ (secThrough_spec W D.xP D.yP hD.equation_P)
    (secThrough_spec W D.xP D.yP hD.equation_P) a 0
  have tt := t x' y' n' e''
  rw [DiamAlg.zlinComb_self_zero] at tt
  rw [diam_eq (A := A) hℓ3 hℓA W a D h x' y' (by rw [relPair_P]; exact tt)]
  show toPoint W x' y' = _
  rw [htoP, e']
  exact dif_pos n'

end FieldCase
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"

end ModularCurve.DiamRing
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"

end
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve.DiamRing"

p2m_open "CategoryTheory AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point.ModularCurve WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal"

theorem solution
    (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity) :
    ∃ diam : ∀ (T : Type) [CommRing T] [Algebra A T],
        WeierstrassCurve T → ℤ → ModularCurve.LevelPData T → ModularCurve.LevelPData T,

      (∀ (T : Type) [Field T] [DecidableEq T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          ModularCurve.LevelRelabelling.toPoint W (diam T W a D).xP (diam T W a D).yP =
            a • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          ModularCurve.IsGamma1Point W ℓ (diam T W a D)) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
          (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T' (W.map f.toRingHom) a (D.map f.toRingHom) = (diam T W a D).map f.toRingHom) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (C : WeierstrassCurve.VariableChange T) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T (C • W) a (D.variableChange C) = (diam T W a D).variableChange C) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a a' : ℤ)
          (haa' : (a : ZMod ℓ) = (a' : ZMod ℓ))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T W a D = diam T W a' D) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsGamma1Point W ℓ D), diam T W 1 D = D) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a b : ℤ)
          (ha : ¬ ((ℓ : ℤ) ∣ a)) (hb : ¬ ((ℓ : ℤ) ∣ b))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D),
          diam T W b (diam T W a D) = diam T W (a * b) D) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D)
          (S : Section W) (hS : IsSectionThrough S D.xP D.yP),
          IsSectionThrough (ModularCurve.LevelRelabelling.zsmulSection (𝒢 T W hΔ) a S) (diam T W a D).xP (diam T W a D).yP) := by
  classical
  refine ⟨ModularCurve.DiamRing.diam A ℓ hℓ3 hℓA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T _ _ _ W hΔ a ha D hD
    exact ModularCurve.DiamRing.toPoint_diam (A := A) hℓ3 hℓA W hΔ a ha D hD
  · intro T _ _ W hΔ a ha D hD
    exact ModularCurve.DiamRing.isGamma1Point_diam (A := A) hℓ3 hℓA W a D ⟨hΔ, hD, ha⟩
  · intro T T' _ _ _ _ f W hΔ a ha D hD
    exact ModularCurve.DiamRing.diam_map (A := A) hℓ3 hℓA f W hΔ a ha D hD
  · intro T _ _ W hΔ C a ha D hD
    exact ModularCurve.DiamRing.diam_variableChange (A := A) hℓ3 hℓA W hΔ C a ha D hD
  · intro T _ _ W hΔ a a' haa' D hD
    exact ModularCurve.DiamRing.diam_congr (A := A) hℓ3 hℓA W hΔ a a' haa' D hD
  · intro T _ _ W hΔ D hD
    exact ModularCurve.DiamRing.diam_one (A := A) hℓ3 hℓA W hΔ D hD
  · intro T _ _ W hΔ a b ha hb D hD
    exact ModularCurve.DiamRing.diam_mul (A := A) hℓ3 hℓA W hΔ a b ha hb D hD
  · intro T _ _ W hΔ a ha D hD S hS
    exact ModularCurve.DiamRing.through_zsmulSection (A := A) hℓ3 hℓA 𝒢 h𝒢O W hΔ a ha D hD S hS

end S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_exists_natural_zsmul_gamma1Point (solution)
