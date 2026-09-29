-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.exists_problemAut_relabel_of_isUnit_det_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/91ca8f62-b012-5ca3-bb71-be5143df5ade

import Mathlib
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
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData
import Theorems.Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_exists_problemAut_relabel_of_isUnit_det_gamma0Pow
p2m_attr_erase "instance" "ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "CategoryTheory AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_problemAut_relabel_of_isUnit_det_gamma0Pow.ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel"

open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "LevelComponent LevelComponent.Raw LevelComponent.Raw.ext' kernelVariableChangeDeg levelPComponent LevelComponent.Raw.mk LevelPData IsLevelPStructure gamma0PowDeg IsGamma0PowAt gamma0PowComponent LevelRelabelling.LevelPData.relabel LevelRelabelling.RawDrinfeldPair.relabel"
namespace LevelRelabelling
p2m_export "ModularCurve.LevelRelabelling" "LevelPData.relabel zsmulSection zlinComb RawDrinfeldPair.relabel IsModuliRelabelling exists_natural_relabel_levelPData RawDrinfeldPair.relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le"
p2m_open "ModularCurve.LevelRelabelling ModularCurve"

namespace T1Drin

variable {T : Type} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))

theorem nsmul_eq_pow (k : ℕ) (P : Section W) :
    letI : Group (Section W) := G.pointGroup _
    G.nsmul _ k P = P ^ k := by
  letI : Group (Section W) := G.pointGroup _
  induction k with
  | zero => rw [pow_zero]; rfl
  | succ k ih =>
    rw [pow_succ, RelativeGroupLaw.nsmul_succ, ih]
    rfl

theorem zsmulSection_eq_zpow (n : ℤ) (P : Section W) :
    letI : Group (Section W) := G.pointGroup _
    zsmulSection G n P = P ^ n := by
  letI : Group (Section W) := G.pointGroup _
  cases n with
  | ofNat k =>
    show G.nsmul _ k P = P ^ ((k : ℕ) : ℤ)
    rw [zpow_natCast]
    exact nsmul_eq_pow G k P
  | negSucc k =>
    show G.inv _ (G.nsmul _ (k + 1) P) = P ^ (Int.negSucc k)
    rw [zpow_negSucc, nsmul_eq_pow]
    rfl

theorem zlinComb_eq (P Q : Section W) (a b : ℤ) :
    letI : Group (Section W) := G.pointGroup _
    zlinComb G P Q a b = P ^ a * Q ^ b := by
  letI : Group (Section W) := G.pointGroup _
  show G.mul _ (zsmulSection G a P) (zsmulSection G b Q) = _
  rw [zsmulSection_eq_zpow, zsmulSection_eq_zpow]
  rfl

theorem zlinComb_one_zero (P Q : Section W) : zlinComb G P Q 1 0 = P := by
  letI : Group (Section W) := G.pointGroup _
  rw [zlinComb_eq]; simp

theorem zlinComb_zero_one (P Q : Section W) : zlinComb G P Q 0 1 = Q := by
  letI : Group (Section W) := G.pointGroup _
  rw [zlinComb_eq]; simp

theorem zlinComb_zlinComb (hcomm : ∀ x y : Section W, G.mul _ x y = G.mul _ y x)
    (P Q : Section W) (a b c d a' b' : ℤ) :
    zlinComb G (zlinComb G P Q a b) (zlinComb G P Q c d) a' b' =
      zlinComb G P Q (a * a' + c * b') (b * a' + d * b') := by
  letI : CommGroup (Section W) := { G.pointGroup _ with mul_comm := hcomm }
  have e : ∀ (P Q : Section W) (a b : ℤ), zlinComb G P Q a b = P ^ a * Q ^ b := fun P Q a b => zlinComb_eq G P Q a b
  rw [e, e, e, e, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, zpow_add, zpow_add,
    mul_mul_mul_comm]

end T1Drin

namespace T1Stubs

theorem relabel_one {A : Type} [CommRing A] (𝒢 : GroupLaws A)
    (T : Type) [CommRing T] [Algebra A T] (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ) :
    RawDrinfeldPair.relabel 𝒢 1 x hΔ = x := by
  obtain ⟨c, P, Q⟩ := x
  show (⟨c, zlinComb (𝒢 T c hΔ) P Q ((1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0),
      zlinComb (𝒢 T c hΔ) P Q ((1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ((1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1)⟩ : RawDrinfeldPair T)
      = ⟨c, P, Q⟩
  have h00 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := rfl
  have h10 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := rfl
  have h01 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := rfl
  have h11 : (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := rfl
  rw [h00, h10, h01, h11, T1Drin.zlinComb_one_zero, T1Drin.zlinComb_zero_one]

theorem relabel_relabel {A : Type} [CommRing A] (𝒢 : GroupLaws A)
    (T : Type) [CommRing T] [Algebra A T] (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hcomm : ∀ P Q : Section x.curve, (𝒢 T x.curve hΔ).mul _ P Q = (𝒢 T x.curve hΔ).mul _ Q P)
    (g h : Matrix (Fin 2) (Fin 2) ℤ) :
    RawDrinfeldPair.relabel 𝒢 h (RawDrinfeldPair.relabel 𝒢 g x hΔ) hΔ = RawDrinfeldPair.relabel 𝒢 (g * h) x hΔ := by
  obtain ⟨c, P, Q⟩ := x
  show (⟨c, zlinComb (𝒢 T c hΔ) (zlinComb (𝒢 T c hΔ) P Q (g 0 0) (g 1 0)) (zlinComb (𝒢 T c hΔ) P Q (g 0 1) (g 1 1)) (h 0 0) (h 1 0),
      zlinComb (𝒢 T c hΔ) (zlinComb (𝒢 T c hΔ) P Q (g 0 0) (g 1 0)) (zlinComb (𝒢 T c hΔ) P Q (g 0 1) (g 1 1)) (h 0 1) (h 1 1)⟩
      : RawDrinfeldPair T)
      = ⟨c, zlinComb (𝒢 T c hΔ) P Q ((g * h) 0 0) ((g * h) 1 0), zlinComb (𝒢 T c hΔ) P Q ((g * h) 0 1) ((g * h) 1 1)⟩
  rw [T1Drin.zlinComb_zlinComb _ hcomm, T1Drin.zlinComb_zlinComb _ hcomm]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]

end T1Stubs

namespace T1Aux

theorem map_castHom_of_dvd {n m : ℕ} (h : m ∣ n) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    (g.map (Int.castRingHom (ZMod n))).map (ZMod.castHom h (ZMod m)) = g.map (Int.castRingHom (ZMod m)) := by
  rw [Matrix.map_map]
  congr 1
  funext z
  simp

theorem isUnit_det_map_of_dvd {n m : ℕ} (h : m ∣ n) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hg : IsUnit (g.map (Int.castRingHom (ZMod n))).det) : IsUnit (g.map (Int.castRingHom (ZMod m))).det := by
  have key := RingHom.map_det (ZMod.castHom h (ZMod m)) (g.map (Int.castRingHom (ZMod n)))
  rw [RingHom.mapMatrix_apply] at key
  rw [← map_castHom_of_dvd h g, ← key]
  exact hg.map _

theorem isUnit_cast_det_of_isUnit_det_map {m : ℕ} (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hg : IsUnit (g.map (Int.castRingHom (ZMod m))).det) : IsUnit ((g.det : ℤ) : ZMod m) := by
  have key := RingHom.map_det (Int.castRingHom (ZMod m)) g
  rw [RingHom.mapMatrix_apply] at key
  rw [← key] at hg
  simpa using hg

theorem map_eq_map_of_mul_map_eq_one_of_dvd {n m : ℕ} (h : m ∣ n) (g g' : Matrix (Fin 2) (Fin 2) ℤ)
    (hgg' : (g * g').map (Int.castRingHom (ZMod n)) = 1) :
    (g * g').map (Int.castRingHom (ZMod m)) = (1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod m)) := by
  rw [← map_castHom_of_dvd h (g * g'), hgg', Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_inverse_mod {n : ℕ} (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hg : IsUnit (g.map (Int.castRingHom (ZMod n))).det) :
    ∃ g' : Matrix (Fin 2) (Fin 2) ℤ,
      (g * g').map (Int.castRingHom (ZMod n)) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod n)) = 1 := by
  have hu : IsUnit (g.map (Int.castRingHom (ZMod n))) := (Matrix.isUnit_iff_isUnit_det _).mpr hg
  obtain ⟨u, hu⟩ := hu
  have key : ((↑u⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod n)).map (fun z : ZMod n => (z.cast : ℤ))).map (Int.castRingHom (ZMod n))
      = (↑u⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
    rw [Matrix.map_map]
    conv_rhs => rw [← Matrix.map_id (↑u⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod n))]
    congr 1
    funext z
    simp [ZMod.intCast_zmod_cast]
  refine ⟨(↑u⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod n)).map (fun z : ZMod n => (z.cast : ℤ)), ?_, ?_⟩
  · rw [Matrix.map_mul, key, ← hu, Units.mul_inv]
  · rw [Matrix.map_mul, key, ← hu, Units.inv_mul]

end T1Aux

namespace T1Build

theorem hgℓ (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det :=
  T1Aux.isUnit_det_map_of_dvd (dvd_mul_left ℓ q) g hg

theorem hgq (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) : IsUnit ((g.det : ℤ) : ZMod q) :=
  T1Aux.isUnit_cast_det_of_isUnit_det_map g (T1Aux.isUnit_det_map_of_dvd (dvd_mul_right q ℓ) g hg)

theorem isUnit_Δ_pair (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    IsUnit x.level.2.2.curve.Δ := by
  obtain ⟨hc, -⟩ := x.isLevel.2.2
  rw [hc]; exact x.isUnit_Δ

def rawRelabel (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T :=
  show LevelComponent.Raw ((gamma0PowComponent A M' hM).prod ((levelPComponent A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))) T from
  LevelComponent.Raw.mk x.curve x.isUnit_Δ
    (x.level.1, (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose T x.curve g x.level.2.1,
      RawDrinfeldPair.relabel 𝒢 g x.level.2.2 (isUnit_Δ_pair q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x))
    (by
      refine And.intro x.isLevel.1 (And.intro ?_ ?_)
      · exact (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose_spec.2.1 T x.curve x.isUnit_Δ g (hgℓ q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg) x.level.2.1 x.isLevel.2.1
      · obtain ⟨hc, hΔ₀, hB⟩ := x.isLevel.2.2
        refine And.intro hc (Exists.intro hΔ₀ ?_)
        exact IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det _
          (GroupLaws.mul_comm_of_isOriginIdentity 𝒢 h𝒢 h𝒢O hVC hCO T _ hΔ₀) q _ _ hB g (hgq q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg))

theorem curve_rawRelabel (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x).curve = x.curve := rfl

theorem level_rawRelabel (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x).level = (x.level.1, (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose T x.curve g x.level.2.1,
      RawDrinfeldPair.relabel 𝒢 g x.level.2.2 (isUnit_Δ_pair q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x)) := rfl

theorem rawRelabel_act (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T : Type} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x) = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x) := by
  refine LevelComponent.Raw.ext' rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · exact (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose_spec.2.2.2.1 T x.curve x.isUnit_Δ C g (hgℓ q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg) x.level.2.1 x.isLevel.2.1
  · exact (LevelTransport.act_relabel_eq_relabel_act 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC hCO T C g x.level.2.2 _ _).symm

theorem rawRelabel_mapRing (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f x) = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x) := by
  refine LevelComponent.Raw.ext' rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · exact (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose_spec.2.2.1 T T' f x.curve x.isUnit_Δ g (hgℓ q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg) x.level.2.1 x.isLevel.2.1
  · exact (LevelTransport.map_relabel_eq_relabel_map 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC hCO T T' f g x.level.2.2 _ _).symm

def sigma (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut where
  act := fun y => Quot.lift (fun x => Quot.mk _ (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x))
    (by
      rintro x y ⟨C, rfl⟩
      exact Quot.sound ⟨C, rawRelabel_act q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg C x⟩) y
  act_map := by
    intro T T' _ _ _ _ f y
    induction y using Quot.ind with
    | mk x =>
      show Quot.mk _ (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f x)) =
        Quot.mk _ ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x))
      rw [rawRelabel_mapRing]
  jOf_act := by
    intro T _ _ y
    induction y using Quot.ind with
    | mk x => rfl

theorem sigma_act_mk (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    (sigma q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg).act (Quot.mk _ x) = Quot.mk _ (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x) := rfl

theorem rawRelabel_rawRelabel (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det)
    (g' : Matrix (Fin 2) (Fin 2) ℤ) (hg' : IsUnit (g'.map (Int.castRingHom (ZMod (q * ℓ)))).det)
    (hgg' : (g * g').map (Int.castRingHom (ZMod (q * ℓ))) = 1)
    {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g' hg' (rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x) = x := by
  refine LevelComponent.Raw.ext' rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  ·
    show (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose T x.curve g' ((exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose T x.curve g x.level.2.1) = x.level.2.1
    rw [(exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose_spec.2.2.2.2.2.2 T x.curve x.isUnit_Δ g g' (hgℓ q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg) (hgℓ q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g' hg') x.level.2.1 x.isLevel.2.1,
      (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose_spec.2.2.2.2.1 T x.curve x.isUnit_Δ (g * g') 1
        (T1Aux.map_eq_map_of_mul_map_eq_one_of_dvd (dvd_mul_left ℓ q) g g' hgg') x.level.2.1 x.isLevel.2.1,
      (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose_spec.2.2.2.2.2.1 T x.curve x.isUnit_Δ x.level.2.1 x.isLevel.2.1]
  ·
    show RawDrinfeldPair.relabel 𝒢 g' (RawDrinfeldPair.relabel 𝒢 g x.level.2.2 (isUnit_Δ_pair q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x))
        (isUnit_Δ_pair q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg x) = x.level.2.2
    rw [T1Stubs.relabel_relabel 𝒢 T x.level.2.2 _ (GroupLaws.mul_comm_of_isOriginIdentity 𝒢 h𝒢 h𝒢O hVC hCO T _ _) g g',
      RawDrinfeldPair.relabel_eq_relabel_of_map_eq_of_isLevel_of_two_le 𝒢 q (Fact.out : q.Prime).two_le T x.curve
        x.level.2.2 _ x.isLevel.2.2 (g * g') 1
        (T1Aux.map_eq_map_of_mul_map_eq_one_of_dvd (dvd_mul_right q ℓ) g g' hgg'),
      T1Stubs.relabel_one]

theorem sigma_act_mk_eq_of_relabel (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) {T : Type} [Field T] [Algebra A T]
    (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ)
    (hc : x'.curve = x.curve) (h1 : x'.level.1 = x.level.1)
    (h21 : x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve g x.level.2.1)
    (h22 : x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ) :
    (sigma q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg).act (Quot.mk _ x) = Quot.mk _ x' := by
  rw [sigma_act_mk]
  congr 1
  refine LevelComponent.Raw.ext' hc.symm (Prod.ext h1.symm (Prod.ext ?_ ?_))
  · show (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose T x.curve g x.level.2.1 = x'.level.2.1
    rw [h21]
    exact (exists_natural_relabel_levelPData A ℓ hℓ3 hℓA).choose_spec.1 T x.curve x.isUnit_Δ g (hgℓ q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg) x.level.2.1 x.isLevel.2.1
  · show RawDrinfeldPair.relabel 𝒢 g x.level.2.2 _ = x'.level.2.2
    rw [h22]

end T1Build

end ModularCurve.LevelRelabelling

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A : Type) [CommRing A] (hℓA : IsUnit ((ℓ : ℕ) : A))
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

    (g : Matrix (Fin 2) (Fin 2) ℤ) (hdet : IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det) :
    ∃ σ σ' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,

      (∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T), σ'.act (σ.act y) = y) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (y : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T), σ.act (σ'.act y) = y) ∧

      (∀ (T : Type) [Field T] [Algebra A T]
          (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
          x'.curve = x.curve →
          x'.level.1 = x.level.1 →
          x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve g x.level.2.1 →
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ →
          σ.act (Quot.mk _ x) = Quot.mk _ x') ∧

      (∃ g' : Matrix (Fin 2) (Fin 2) ℤ,
        (g * g').map (Int.castRingHom (ZMod (q * ℓ))) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod (q * ℓ))) = 1 ∧
        (∀ (T : Type) [Field T] [Algebra A T]
          (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
          x'.curve = x.curve →
          x'.level.1 = x.level.1 →
          x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve g' x.level.2.1 →
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g' x.level.2.2 hΔ →
          σ'.act (Quot.mk _ x) = Quot.mk _ x')) := by
  obtain ⟨g', hgg', hg'g⟩ := ModularCurve.LevelRelabelling.T1Aux.exists_inverse_mod g hdet
  have hdet' : IsUnit (g'.map (Int.castRingHom (ZMod (q * ℓ)))).det := by
    have h := congrArg Matrix.det hg'g
    rw [Matrix.map_mul, Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  refine ⟨ModularCurve.LevelRelabelling.T1Build.sigma q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hdet,
    ModularCurve.LevelRelabelling.T1Build.sigma q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g' hdet', ?_, ?_, ?_, ⟨g', hgg', hg'g, ?_⟩⟩
  · intro T _ _ y
    induction y using Quot.ind with
    | mk x =>
      rw [ModularCurve.LevelRelabelling.T1Build.sigma_act_mk, ModularCurve.LevelRelabelling.T1Build.sigma_act_mk,
        ModularCurve.LevelRelabelling.T1Build.rawRelabel_rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hdet g' hdet' hgg']
  · intro T _ _ y
    induction y using Quot.ind with
    | mk x =>
      rw [ModularCurve.LevelRelabelling.T1Build.sigma_act_mk, ModularCurve.LevelRelabelling.T1Build.sigma_act_mk,
        ModularCurve.LevelRelabelling.T1Build.rawRelabel_rawRelabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g' hdet' g hdet hg'g]
  · intro T _ _ x x' hΔ hc h1 h21 h22
    exact ModularCurve.LevelRelabelling.T1Build.sigma_act_mk_eq_of_relabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hdet x x' hΔ hc h1 h21 h22
  · intro T _ _ x x' hΔ hc h1 h21 h22
    exact ModularCurve.LevelRelabelling.T1Build.sigma_act_mk_eq_of_relabel q M' ℓ hℓ3 A hℓA hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g' hdet' x x' hΔ hc h1 h21 h22

end

end S_ModularCurve_LevelRelabelling_exists_problemAut_relabel_of_isUnit_det_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_exists_problemAut_relabel_of_isUnit_det_gamma0Pow (solution)
