-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/bd06e6e0-b2fb-595e-accf-96178adb7a82

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
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Theorems.Thm_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_pins_restrictScalars
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

noncomputable section
namespace AutIdentUnr

universe u

variable (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q ℓ M' : ℕ)
  [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
  (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
      ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
  (hM : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
      ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
  (hℓ' : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
      ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
  (hM' : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
      ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
  (𝒢 : GroupLaws A₀) (𝒯 : LevelTransport A₀ 𝒢 q)

abbrev D₀ := rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯

abbrev DA := rigidDataPow A ℓ M' q hℓ' hM' (𝒢.restrictScalars A) (𝒯.restrictScalars A)

variable {T : Type u} [CommRing T] [Algebra A T]

def toA : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).Raw T) →
    (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).Raw T :=
  fun r => letI : Algebra A₀ T := algebraRestrict A₀ A T
    ⟨r.curve, r.isUnit_Δ, r.level, r.isLevel⟩

def toA₀ : (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).Raw T →
    (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).Raw T) :=
  fun r => letI : Algebra A₀ T := algebraRestrict A₀ A T
    ⟨r.curve, r.isUnit_Δ, r.level, r.isLevel⟩

theorem toA₀_toA (r : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).Raw T)) :
    toA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r) = r := by
  rcases r with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩; rfl

theorem toA_toA₀ (r : (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).Raw T) :
    toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (toA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r) = r := by
  rcases r with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩; rfl

theorem act_toA (C : WeierstrassCurve.VariableChange T)
    (r : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).Raw T)) :
    (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).act C (toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r) =
      toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯
        (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).act C r) := by
  rcases r with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩; rfl

theorem act_toA₀ (C : WeierstrassCurve.VariableChange T) (r : (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).Raw T) :
    (letI : Algebra A₀ T := algebraRestrict A₀ A T;
      (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).act C (toA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r)) =
      toA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 ((DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).act C r) := by
  rcases r with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩; rfl

theorem mapRing_toA {T' : Type u} [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (r : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).Raw T)) :
    (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).mapRing f (toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r) =
      toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯
        (letI : Algebra A₀ T := algebraRestrict A₀ A T; letI : Algebra A₀ T' := algebraRestrict A₀ A T'
         (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).mapRing (algHomRestrict A₀ A f) r) := by
  rcases r with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩; rfl

def ptToA : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T) →
    (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.Pt T :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  Quot.map (toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯) (fun x y h => by
    obtain ⟨C, rfl⟩ := h
    exact ⟨C, (act_toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 C x).symm⟩)

def ptToA₀ : (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.Pt T →
    (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T) :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  Quot.map (toA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯) (fun x y h => by
    obtain ⟨C, rfl⟩ := h
    exact ⟨C, (act_toA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 C x).symm⟩)

theorem ptToA_mk (r : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).Raw T)) :
    ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (Quot.mk _ r) = Quot.mk _ (toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r) := rfl

theorem ptToA₀_mk (r : (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).Raw T) :
    ptToA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (Quot.mk _ r) = Quot.mk _ (toA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r) := rfl

theorem ptToA₀_ptToA (x : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T)) :
    ptToA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 x) = x := by
  induction x using Quot.ind with | mk r => ?_
  rw [ptToA_mk, ptToA₀_mk, toA₀_toA]

theorem ptToA_ptToA₀ (x : (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.Pt T) :
    ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (ptToA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 x) = x := by
  induction x using Quot.ind with | mk r => ?_
  rw [ptToA₀_mk, ptToA_mk, toA_toA₀]

theorem jOf_ptToA (x : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T)) :
    (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.jOf (ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 x) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x) := by
  induction x using Quot.ind with | mk r => ?_
  rcases r with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩; rfl

theorem map_ptToA {T' : Type u} [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : (letI : Algebra A₀ T := algebraRestrict A₀ A T; (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T)) :
    (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.map f (ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 x) =
      ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯
        (letI : Algebra A₀ T := algebraRestrict A₀ A T; letI : Algebra A₀ T' := algebraRestrict A₀ A T'
         (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (algHomRestrict A₀ A f) x) := by
  induction x using Quot.ind with | mk r => ?_
  show Quot.mk _ ((DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).mapRing f (toA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 r)) = _
  rw [mapRing_toA]
  rfl

theorem map_ptToA₀ {T' : Type u} [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.Pt T) :
    (letI : Algebra A₀ T := algebraRestrict A₀ A T; letI : Algebra A₀ T' := algebraRestrict A₀ A T'
      (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (algHomRestrict A₀ A f) (ptToA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 x)) =
      ptToA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 ((DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.map f x) := by
  induction x using Quot.ind with | mk r => ?_
  rcases r with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩; rfl

def restrictAut (σ : (D₀ A₀ q ℓ M' hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut) :
    (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.ProblemAut where
  act {T} _ _ x :=
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (σ.act (ptToA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 x))
  act_map {T T'} _ _ _ _ f x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    show ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (σ.act (ptToA₀ A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 (_))) = _
    rw [← map_ptToA₀, σ.act_map, ← map_ptToA]
  jOf_act {T} _ _ x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    show (DA A₀ A q ℓ M' hℓ' hM' 𝒢 𝒯).toLevelModuliDatum.jOf (ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯 _) = _
    rw [jOf_ptToA, σ.jOf_act, ← jOf_ptToA A₀ A q ℓ M' hℓ hM hℓ' hM' 𝒢 𝒯, ptToA_ptToA₀]

end AutIdentUnr
end

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

    (A₀ : Type) [CommRing A₀] [Algebra A₀ L] [Algebra A₀ ↥K] [IsScalarTower A₀ L ↥K]
    [Algebra A₀ A] [IsScalarTower A₀ A ↥K]

    (hℓA : IsUnit ((ℓ : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (ρ : ↥(CongruenceSubgroup.Gamma0 M') → (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut)

    (hρ : ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A₀ T]
      (x x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρ γ).act (Quot.mk _ x) = Quot.mk _ x') :
    ∃ x₀ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K,
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) ∧

      (haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L)) (r : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K),
      (Quot.mk _ r : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x₀ ∧

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy)) ∧
      ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K),
        ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A₀) x₀ = (ρ ⟨γ, hγ⟩).act x₀ := by
  classical

  have hinstK : (‹Algebra A₀ ↥K›) = algebraRestrict A₀ A ↥K :=
    Algebra.algebra_ext _ _ (fun r => IsScalarTower.algebraMap_apply A₀ A ↥K r)
  subst hinstK
  letI instK : Algebra A₀ ↥K := algebraRestrict A₀ A ↥K

  have hℓ_A : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C) := fun T _ _ W C D h => by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact hℓ T W C D h
  have hM_A : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h) :=
    fun T _ _ W C p k h hh => by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact hM T W C p k h hh
  have hVC_A : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ := fun T _ _ W C => by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact hVC T W C
  obtain ⟨h𝒢_A, h𝒢O_A, h𝒯_A, hCO_A⟩ :=
    WeierstrassCurve.DrinfeldGlobal.pins_restrictScalars A₀ A q 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hCO
  have hℓA_A : IsUnit ((ℓ : ℕ) : A) := by simpa using hℓA.map (algebraMap A₀ A)
  have hM'A_A : IsUnit ((M' : ℕ) : A) := by simpa using hM'A.map (algebraMap A₀ A)

  let ρA : ↥(CongruenceSubgroup.Gamma0 M') →
      (AutIdentUnr.DA A₀ A q ℓ M' hℓ_A hM_A 𝒢 𝒯).toLevelModuliDatum.ProblemAut :=
    fun γ => AutIdentUnr.restrictAut A₀ A q ℓ M' hℓ hM hℓ_A hM_A 𝒢 𝒯 (ρ γ)
  have hρA : ∀ (γ : ↥(CongruenceSubgroup.Gamma0 M')) (T : Type) [Field T] [Algebra A T]
      (x x' : (AutIdentUnr.DA A₀ A q ℓ M' hℓ_A hM_A 𝒢 𝒯).Raw T) (hΔ : IsUnit x.level.2.2.curve.Δ),
      x'.curve = x.curve →
      x'.level.1 = x.level.1 →
      x'.level.2.1 = ModularCurve.LevelRelabelling.LevelPData.relabel x.curve
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.1 →
      x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel (𝒢.restrictScalars A)
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) x.level.2.2 hΔ →
      (ρA γ).act (Quot.mk _ x) = Quot.mk _ x' := by
    intro γ T _ _ x x' hΔ h1 h2 h3 h4
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    rcases x with ⟨W, hΔx, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩
    rcases x' with ⟨W', hΔx', ⟨h', D', z'⟩, ⟨hh', hD', hz'⟩⟩
    have key := hρ γ T ⟨W, hΔx, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ ⟨W', hΔx', ⟨h', D', z'⟩, ⟨hh', hD', hz'⟩⟩ hΔ h1 h2 h3 h4
    show AutIdentUnr.ptToA A₀ A q ℓ M' hℓ hM hℓ_A hM_A 𝒢 𝒯
      ((ρ γ).act (AutIdentUnr.ptToA₀ A₀ A q ℓ M' hℓ hM hℓ_A hM_A 𝒢 𝒯 (Quot.mk _ _))) = _
    rw [AutIdentUnr.ptToA₀_mk]
    show AutIdentUnr.ptToA A₀ A q ℓ M' hℓ hM hℓ_A hM_A 𝒢 𝒯 ((ρ γ).act (Quot.mk _ ⟨W, hΔx, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩)) = _
    rw [key]
    rfl

  obtain ⟨xA, hjA, ⟨C, rA, hrA, hi, hii, hvi, hiii, hiv⟩, heq⟩ :=
    ModularCurve.FullLevel.exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK A hAq j hj hℓA_A hM'A_A hℓ_A hM_A
      (𝒢.restrictScalars A) h𝒢_A h𝒢O_A (𝒯.restrictScalars A) h𝒯_A hVC_A hCO_A ρA hρA

  refine ⟨AutIdentUnr.ptToA₀ A₀ A q ℓ M' hℓ hM hℓ_A hM_A 𝒢 𝒯 xA, ?_, ?_, ?_⟩
  ·
    rw [← hjA, ← AutIdentUnr.jOf_ptToA A₀ A q ℓ M' hℓ hM hℓ_A hM_A 𝒢 𝒯, AutIdentUnr.ptToA_ptToA₀]
  ·
    rcases rA with ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩
    refine ⟨C, ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩, ?_, hi, hii, hvi, hiii, hiv⟩
    rw [← hrA, AutIdentUnr.ptToA₀_mk]
    rfl
  · intro γ hγ τ hτ
    have h := heq γ hγ τ hτ
    have hres : ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A₀) =
        algHomRestrict A₀ A ((τ.toAlgHom : ↥K →ₐ[L] ↥K).restrictScalars A) := AlgHom.ext (fun _ => rfl)
    rw [hres, AutIdentUnr.map_ptToA₀, h]
    exact AutIdentUnr.ptToA₀_ptToA A₀ A q ℓ M' hℓ hM hℓ_A hM_A 𝒢 𝒯 _

end S_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_pt_forall_isLevelAutAt_map_eq_act_of_exists_ringHom_gamma0Pow_of_tate_of_algebra_of_isScalarTower (solution)
