-- Prove2me | solution 1 for ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9634f1e7-889e-5f01-b451-d39fe0340006

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Definitions.Def_ModularCurve_KatzLevelPTorusPairs
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_TensorProduct_eq_zero_of_forall_lTensor_eq_zero_of_field
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Theorems.Thm_ModularCurve_map_coeffMap_tateLaurent
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_cuspData_map_coeffMap
import Theorems.Thm_ModularCurve_LevelP_flat_univBasisRing_vcRing_borelRing
import Theorems.Thm_ModularCurve_isUnit_indepElt_symm
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Theorems.Thm_LaurentSeries_exists_fg_subalgebra_isUnit_map_of_isUnit_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

noncomputable section

p2m_open "Polynomial WeierstrassCurve~cusp"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand indepElt indepElt_map LevelPData LevelPData.map_xP LevelPData.map_yP LevelPData.map_xQ LevelPData.map_yQ LevelPData.map_id LevelPData.map_map LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ IsLevelPStructure KatzLevelPForm KatzLevelPForm.ext KatzLevelPForm.zero_toFun LevelPData.xP LevelPData.ext LevelPData.xQ cuspData algebraMap_laurentSeries_apply isUnit_Δ_tateBase tateBase coeffMap coeffMap_coeff LevelP.UnivBasisRing KatzLevelPForm.univInclude KatzLevelPForm.univCurveOver KatzLevelPForm.isUnit_Δ_univCurveOver KatzLevelPForm.univDataOver KatzLevelPForm.isLevelPStructure_univDataOver KatzLevelPForm.evalUniv map_coeffMap_tateLaurent coeffMap_qExpand cuspData_map_coeffMap isUnit_indepElt_symm"
namespace QExpSplitDevissage
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.ModularCurve ModularCurve.LevelP"
open scoped TensorProduct

section Generalities

variable {R : Type u} [CommRing R] {p : ℕ} {k : ℤ}

theorem toFun_congr (G : KatzLevelPForm R p k) {A : Type u} [CommRing A] [Algebra R A]
    {W W' : WeierstrassCurve A} (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) {D D' : LevelPData A}
    (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W' p D') (e : W = W') (e' : D = D') :
    G.toFun W hW D hD = G.toFun W' hW' D' hD' := by
  subst e e'
  rfl

theorem map_toFun' (G : KatzLevelPForm R p k) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    f (G.toFun W hW D hD) = G.toFun (W.map (f : A →+* B)) (KatzModularForm.isUnit_Δ_map _ hW)
      (D.map (f : A →+* B)) (hD.map _) :=
  (G.map_toFun f W hW _ D hD _).symm

end Generalities

namespace LevelPData
private theorem _root_.ModularCurve.QExpSplitDevissage.LevelPData.map_variableChange {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).map φ = (D.map φ).variableChange (C.map φ) := by
  have hu : φ ((C.u⁻¹ : Aˣ) : A) = (((C.map φ).u⁻¹ : Bˣ) : B) := (Units.coe_map_inv (φ : A →* B) C.u).symm
  refine LevelPData.ext ?_ ?_ ?_ ?_ <;>
    simp only [LevelPData.map_xP, LevelPData.map_yP, LevelPData.map_xQ, LevelPData.map_yQ,
      LevelPData.variableChange_xP, LevelPData.variableChange_yP, LevelPData.variableChange_xQ,
      LevelPData.variableChange_yQ, map_mul, map_sub, map_pow, hu, VariableChange.map]

end LevelPData
p2m_export "ModularCurve.QExpSplitDevissage" "LevelPData.map_variableChange"

section Forms

variable (p : ℕ)

theorem isLevelPStructure_vcData' :
    IsLevelPStructure (univVC p • vcCurve p) p ((vcData p).variableChange (univVC p)) :=
  (isLevelPStructure_vcData p).variableChange (univVC p)

theorem isUnit_pΔ_vcCurve' : IsUnit ((p : VCRing p) * (univVC p • vcCurve p).Δ) := by
  refine (isUnit_natCast_vcRing p).mul ?_
  rw [variableChange_Δ]
  exact ((Units.isUnit _).pow 12).mul (isUnit_Δ_vcCurve p)

def vcBeta : UnivBasisRing p →+* VCRing p :=
  UnivBasisRing.classify p (univVC p • vcCurve p) (isUnit_pΔ_vcCurve' p) _ (isLevelPStructure_vcData' p)

theorem univCurveT_map_vcBeta : (univCurveT p).map (vcBeta p) = univVC p • vcCurve p :=
  univCurveT_map_classify p _ _ _ _

theorem univData_map_vcBeta : (univData p).map (vcBeta p) = (vcData p).variableChange (univVC p) :=
  univData_map_classify p _ _ _ _

def vcForm (k : ℤ) : UnivBasisRing p →ₗ[ℤ] VCRing p where
  toFun t := vcBeta p t - (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p t
  map_add' x y := by simp only [map_add]; ring
  map_smul' n x := by simp only [zsmul_eq_mul, eq_intCast, Int.cast_id, map_mul, map_intCast]; ring

theorem vcForm_apply (k : ℤ) (t : UnivBasisRing p) :
    vcForm p k t = vcBeta p t - (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) * VCRing.ofUniv p t := rfl

variable [Fact p.Prime] (hp2 : p ≠ 2)

theorem not_dvd_of_le {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) : ¬ (p : ℤ) ∣ (a : ℤ) := by
  intro h
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h' : p ∣ a := Int.natCast_dvd_natCast.mp h
  have hle : p ≤ a := Nat.le_of_dvd ha h'
  omega

include hp2 in
theorem isUnit_ΨSq_univP {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    IsUnit (((univCurveT p).ΨSq a).eval (univData p).xP) :=
  ((univCurveT p).eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p))
    (isLevelPStructure_univData p).preΨ_P (not_dvd_of_le p ha ha')).1

include hp2 in
theorem isUnit_ΨSq_univQ {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    IsUnit (((univCurveT p).ΨSq a).eval (univData p).xQ) :=
  ((univCurveT p).eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p))
    (isLevelPStructure_univData p).preΨ_Q (not_dvd_of_le p ha ha')).1

include hp2 in

theorem eval_preΨ_torusX {a : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    ((univCurveT p).preΨ p).eval (torusX p a) = 0 :=
  ((univCurveT p).eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p))
    (isLevelPStructure_univData p).preΨ_P (not_dvd_of_le p ha ha')).2

include hp2 in

theorem eval_preΨ_borelX {b : ℕ} (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2) :
    ((univCurveT p).preΨ p).eval (borelX p b) = 0 :=
  ((univCurveT p).eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero hp2
    ((isUnit_natCast_univBasisRing p).mul (isUnit_Δ_univCurveT p))
    (isLevelPStructure_univData p).preΨ_Q (not_dvd_of_le p hb hb')).2

include hp2 in

theorem isLevelPStructure_torusData' {a b : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2)
    (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2) :
    IsLevelPStructure (torusCurve p a b) p (torusData' p a b) := by
  have hΨP := eval_preΨ_torusX p hp2 ha ha'
  have hΨQ := eval_preΨ_borelX p hp2 hb hb'
  have hden := isUnit_algebraMap_torusDenom p a b
  rw [torusDenom, map_mul] at hden
  rw [torusCurve_eq_map_torusQCurve]
  exact
  { equation_P := equation_map _ (equation_torusQ_P p a b)
    equation_Q := equation_map _ (equation_torusQ_Q p a b)
    preΨ_P := by
      show (((torusQCurve p a b).map (algebraMap (TorusQRing p a b) (TorusRing p a b))).preΨ p).eval
        (algebraMap _ _ (TorusQRing.xP p a b)) = 0
      rw [preΨ_eval_map, TorusQRing.xP, torusQCurve, preΨ_eval_map, hΨP, map_zero, map_zero]
    preΨ_Q := by
      show (((torusQCurve p a b).map (algebraMap (TorusQRing p a b) (TorusRing p a b))).preΨ p).eval
        (algebraMap _ _ (TorusQRing.xQ p a b)) = 0
      rw [preΨ_eval_map, TorusQRing.xQ, torusQCurve, preΨ_eval_map, hΨQ, map_zero, map_zero]
    isUnit_indepElt_PQ := by
      show IsUnit (indepElt ((torusQCurve p a b).map (algebraMap (TorusQRing p a b) (TorusRing p a b))) p
        (algebraMap _ _ (TorusQRing.xP p a b)) (algebraMap _ _ (TorusQRing.xQ p a b)))
      rw [indepElt_map]
      exact isUnit_of_mul_isUnit_left hden
    isUnit_indepElt_QP := by
      show IsUnit (indepElt ((torusQCurve p a b).map (algebraMap (TorusQRing p a b) (TorusRing p a b))) p
        (algebraMap _ _ (TorusQRing.xQ p a b)) (algebraMap _ _ (TorusQRing.xP p a b)))
      rw [indepElt_map]
      exact isUnit_of_mul_isUnit_right hden }

omit [Fact p.Prime] in
theorem isUnit_pΔ_torusCurve (a b : ℕ) : IsUnit ((p : TorusRing p a b) * (torusCurve p a b).Δ) :=
  (isUnit_natCast_torusRing p a b).mul (isUnit_Δ_torusCurve p a b)

def torusBeta (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2) :
    UnivBasisRing p →+* TorusRing p a b :=
  UnivBasisRing.classify p (torusCurve p a b) (isUnit_pΔ_torusCurve p a b) (torusData' p a b)
    (isLevelPStructure_torusData' p hp2 ha ha' hb hb')

theorem univCurveT_map_torusBeta (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b)
    (hb' : b ≤ (p - 1) / 2) : (univCurveT p).map (torusBeta p hp2 a b ha ha' hb hb') = torusCurve p a b :=
  univCurveT_map_classify p _ _ _ _

theorem univData_map_torusBeta (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b)
    (hb' : b ≤ (p - 1) / 2) : (univData p).map (torusBeta p hp2 a b ha ha' hb hb') = torusData' p a b :=
  univData_map_classify p _ _ _ _

def torusForm (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2) :
    UnivBasisRing p →ₗ[ℤ] TorusRing p a b where
  toFun t := torusBeta p hp2 a b ha ha' hb hb' t - TorusRing.ofUniv p a b t
  map_add' x y := by simp only [map_add]; ring
  map_smul' n x := by simp only [zsmul_eq_mul, eq_intCast, Int.cast_id, map_mul, map_intCast]; ring

theorem torusForm_apply (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b)
    (hb' : b ≤ (p - 1) / 2) (t : UnivBasisRing p) :
    torusForm p hp2 a b ha ha' hb hb' t = torusBeta p hp2 a b ha ha' hb hb' t - TorusRing.ofUniv p a b t := rfl

end Forms

section Yoneda

variable (p : ℕ) (S : Type u) [CommRing S] {A : Type u} [CommRing A] [Algebra S A]

def sClassify (hpA : IsUnit (p : A)) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) : S ⊗[ℤ] UnivBasisRing p →ₐ[S] A :=
  Algebra.TensorProduct.lift (Algebra.ofId S A)
    (UnivBasisRing.classify p W (hpA.mul hW) D hD).toIntAlgHom (fun _ _ => Commute.all _ _)

variable (hpA : IsUnit (p : A)) (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
  (hD : IsLevelPStructure W p D)

@[scoped simp] theorem sClassify_tmul (s : S) (t : UnivBasisRing p) :
    sClassify p S hpA W hW D hD (s ⊗ₜ t) = algebraMap S A s * UnivBasisRing.classify p W (hpA.mul hW) D hD t :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem sClassify_comp_univInclude :
    (sClassify p S hpA W hW D hD : S ⊗[ℤ] UnivBasisRing p →+* A).comp (KatzLevelPForm.univInclude S p) =
      UnivBasisRing.classify p W (hpA.mul hW) D hD := by
  ext t
  show sClassify p S hpA W hW D hD ((1 : S) ⊗ₜ t) = _
  rw [sClassify_tmul, map_one, one_mul]

theorem univCurveOver_map_sClassify :
    (KatzLevelPForm.univCurveOver S p).map (sClassify p S hpA W hW D hD : S ⊗[ℤ] UnivBasisRing p →+* A) = W := by
  rw [KatzLevelPForm.univCurveOver, WeierstrassCurve.map_map, sClassify_comp_univInclude,
    univCurveT_map_classify]

theorem univDataOver_map_sClassify :
    (KatzLevelPForm.univDataOver S p).map (sClassify p S hpA W hW D hD : S ⊗[ℤ] UnivBasisRing p →+* A) = D := by
  rw [KatzLevelPForm.univDataOver, LevelPData.map_map, sClassify_comp_univInclude,
    univData_map_classify]

theorem sAlgHom_ext {φ ψ : S ⊗[ℤ] UnivBasisRing p →ₐ[S] A}
    (hW : (KatzLevelPForm.univCurveOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) =
      (KatzLevelPForm.univCurveOver S p).map (ψ : S ⊗[ℤ] UnivBasisRing p →+* A))
    (hD : (KatzLevelPForm.univDataOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) =
      (KatzLevelPForm.univDataOver S p).map (ψ : S ⊗[ℤ] UnivBasisRing p →+* A)) : φ = ψ := by
  have h : (φ : S ⊗[ℤ] UnivBasisRing p →+* A).comp (KatzLevelPForm.univInclude S p) =
      (ψ : S ⊗[ℤ] UnivBasisRing p →+* A).comp (KatzLevelPForm.univInclude S p) := by
    refine UnivBasisRing.ringHom_ext p ?_ ?_
    · simpa only [KatzLevelPForm.univCurveOver, WeierstrassCurve.map_map] using hW
    · simpa only [KatzLevelPForm.univDataOver, LevelPData.map_map] using hD
  refine Algebra.TensorProduct.ext' fun s t => ?_
  have hs : s ⊗ₜ[ℤ] t = s • ((1 : S) ⊗ₜ[ℤ] t) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul]
  congr 1
  exact RingHom.congr_fun h t

theorem eq_sClassify {φ : S ⊗[ℤ] UnivBasisRing p →ₐ[S] A}
    (hφW : (KatzLevelPForm.univCurveOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) = W)
    (hφD : (KatzLevelPForm.univDataOver S p).map (φ : S ⊗[ℤ] UnivBasisRing p →+* A) = D) :
    φ = sClassify p S hpA W hW D hD :=
  sAlgHom_ext p S (by rw [hφW, univCurveOver_map_sClassify]) (by rw [hφD, univDataOver_map_sClassify])

theorem sClassify_self (hpS : IsUnit (p : S ⊗[ℤ] UnivBasisRing p)) :
    sClassify p S hpS (KatzLevelPForm.univCurveOver S p) (KatzLevelPForm.isUnit_Δ_univCurveOver S p)
      (KatzLevelPForm.univDataOver S p) (KatzLevelPForm.isLevelPStructure_univDataOver S p) =
      AlgHom.id S _ :=
  (eq_sClassify p S _ _ _ _ _ (by exact WeierstrassCurve.map_id _) (by exact LevelPData.map_id _)).symm

theorem comp_sClassify {A' : Type u} [CommRing A'] [Algebra S A'] (f : A →ₐ[S] A')
    (hpA' : IsUnit (p : A')) (hW' : IsUnit (W.map (f : A →+* A')).Δ)
    (hD' : IsLevelPStructure (W.map (f : A →+* A')) p (D.map (f : A →+* A'))) :
    f.comp (sClassify p S hpA W hW D hD) = sClassify p S hpA' (W.map (f : A →+* A')) hW' (D.map (f : A →+* A')) hD' :=
  eq_sClassify p S _ _ _ _ _
    (by rw [AlgHom.comp_toRingHom, ← WeierstrassCurve.map_map, univCurveOver_map_sClassify])
    (by rw [AlgHom.comp_toRingHom, ← LevelPData.map_map, univDataOver_map_sClassify])

theorem toFun_eq_sClassify_evalUniv {k : ℤ} (G : KatzLevelPForm S p k) :
    G.toFun W hW D hD = sClassify p S hpA W hW D hD G.evalUniv := by
  rw [KatzLevelPForm.evalUniv, map_toFun' G (sClassify p S hpA W hW D hD)]
  exact (toFun_congr G _ _ _ _ (univCurveOver_map_sClassify p S hpA W hW D hD)
    (univDataOver_map_sClassify p S hpA W hW D hD)).symm

end Yoneda

section Targets

variable (p : ℕ) (S : Type u) [CommRing S] {A : Type u} [CommRing A] [Algebra S A]
  (hpA : IsUnit (p : A))

def sLift {N : Type} [CommRing N] (θ : N →+* A) : S ⊗[ℤ] N →ₐ[S] A :=
  Algebra.TensorProduct.lift (Algebra.ofId S A) θ.toIntAlgHom (fun _ _ => Commute.all _ _)

@[scoped simp] theorem sLift_tmul {N : Type} [CommRing N] (θ : N →+* A) (s : S) (n : N) :
    sLift S θ (s ⊗ₜ n) = algebraMap S A s * θ n :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem sLift_lTensor {N : Type} [CommRing N] (β ι : UnivBasisRing p →+* N) (c : N)
    (form : UnivBasisRing p →ₗ[ℤ] N) (hform : ∀ t, form t = β t - c * ι t) (θ : N →+* A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D)
    (W' : WeierstrassCurve A) (hW' : IsUnit W'.Δ) (D' : LevelPData A) (hD' : IsLevelPStructure W' p D')
    (hι : θ.comp ι = UnivBasisRing.classify p W (hpA.mul hW) D hD)
    (hβ : θ.comp β = UnivBasisRing.classify p W' (hpA.mul hW') D' hD') (g : S ⊗[ℤ] UnivBasisRing p) :
    sLift S θ (LinearMap.lTensor S form g) =
      sClassify p S hpA W' hW' D' hD' g - θ c * sClassify p S hpA W hW D hD g := by
  induction g using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [LinearMap.lTensor_tmul, sLift_tmul, hform, sClassify_tmul, sClassify_tmul, ← hι, ← hβ,
      RingHom.comp_apply, RingHom.comp_apply, map_sub, map_mul]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; ring

section VCTarget

variable (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A) (hD : IsLevelPStructure W p D)
  (C : VariableChange A) (hW' : IsUnit (C • W).Δ) (hD' : IsLevelPStructure (C • W) p (D.variableChange C))

def vcTheta : VCRing p →+* A := VCRing.lift p (UnivBasisRing.classify p W (hpA.mul hW) D hD) C

theorem vcTheta_comp_ofUniv : (vcTheta p hpA W hW D hD C).comp (VCRing.ofUniv p) =
    UnivBasisRing.classify p W (hpA.mul hW) D hD :=
  VCRing.lift_comp_ofUniv p _ C

theorem univVC_map_vcTheta : (univVC p).map (vcTheta p hpA W hW D hD C) = C := univVC_map_lift p _ C

theorem vcTheta_comp_vcBeta : (vcTheta p hpA W hW D hD C).comp (vcBeta p) =
    UnivBasisRing.classify p (C • W) (hpA.mul hW') (D.variableChange C) hD' := by
  refine UnivBasisRing.eq_classify p _ _ _ _ ?_ ?_
  · rw [← WeierstrassCurve.map_map, univCurveT_map_vcBeta, ← WeierstrassCurve.map_variableChange,
      univVC_map_vcTheta, vcCurve, WeierstrassCurve.map_map, vcTheta_comp_ofUniv, univCurveT_map_classify]
  · rw [← LevelPData.map_map, univData_map_vcBeta, LevelPData.map_variableChange, univVC_map_vcTheta, vcData,
      LevelPData.map_map, vcTheta_comp_ofUniv, univData_map_classify]

theorem vcTheta_units (k : ℤ) :
    vcTheta p hpA W hW D hD C (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) = ((C.u⁻¹ ^ k : Aˣ) : A) := by
  have hu : Units.map (vcTheta p hpA W hW D hD C : VCRing p →* A) (univVC p).u = C.u :=
    congrArg VariableChange.u (univVC_map_vcTheta p hpA W hW D hD C)
  show (vcTheta p hpA W hW D hD C : VCRing p →* A) (((univVC p).u⁻¹ ^ k : (VCRing p)ˣ) : VCRing p) = _
  rw [← Units.coe_map, map_zpow, map_inv, hu]

theorem vc_eval (k : ℤ) (g : S ⊗[ℤ] UnivBasisRing p) :
    sClassify p S hpA (C • W) hW' (D.variableChange C) hD' g - ((C.u⁻¹ ^ k : Aˣ) : A) * sClassify p S hpA W hW D hD g =
      sLift S (vcTheta p hpA W hW D hD C) (LinearMap.lTensor S (vcForm p k) g) := by
  rw [sLift_lTensor p S hpA (vcBeta p) (VCRing.ofUniv p) _ (vcForm p k) (vcForm_apply p k)
    (vcTheta p hpA W hW D hD C) W hW D hD (C • W) hW' _ hD' (vcTheta_comp_ofUniv p hpA W hW D hD C)
    (vcTheta_comp_vcBeta p hpA W hW D hD C hW' hD') g, vcTheta_units]

end VCTarget

section TorusTarget

variable [Fact p.Prime] (hp2 : p ≠ 2)
  (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D D' : LevelPData A) (hD : IsLevelPStructure W p D)
  (hD' : IsLevelPStructure W p D') {a b : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2)
  (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2)
  (heqP : D'.xP * (W.ΨSq a).eval D.xP = (W.Φ a).eval D.xP)
  (heqQ : D'.xQ * (W.ΨSq b).eval D.xQ = (W.Φ b).eval D.xQ)

omit [Fact p.Prime] in

theorem eq_classify_mul_inverse (x₀ : UnivBasisRing p) {x xA : A} (n : ℕ)
    (hu : IsUnit (((univCurveT p).ΨSq n).eval x₀))
    (hx : UnivBasisRing.classify p W (hpA.mul hW) D hD x₀ = xA)
    (heq : x * (W.ΨSq n).eval xA = (W.Φ n).eval xA) :
    x = UnivBasisRing.classify p W (hpA.mul hW) D hD
      (((univCurveT p).Φ n).eval x₀ * Ring.inverse (((univCurveT p).ΨSq n).eval x₀)) := by
  set φ := UnivBasisRing.classify p W (hpA.mul hW) D hD with hφ
  obtain ⟨v, hv⟩ := hu
  have hWφ : (univCurveT p).map φ = W := univCurveT_map_classify p _ _ _ _
  have hΨ : φ (((univCurveT p).ΨSq n).eval x₀) = (W.ΨSq n).eval xA := by
    rw [← hx, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_ΨSq, hWφ]
  have hΦ : φ (((univCurveT p).Φ n).eval x₀) = (W.Φ n).eval xA := by
    rw [← hx, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_Φ, hWφ]
  rw [map_mul, hΦ, ← hv, Ring.inverse_unit]
  set vA : Aˣ := Units.map (φ : UnivBasisRing p →* A) v with hvA
  have hinv : φ ((v⁻¹ : (UnivBasisRing p)ˣ) : UnivBasisRing p) = ((vA⁻¹ : Aˣ) : A) :=
    (Units.coe_map_inv (φ : UnivBasisRing p →* A) v).symm
  have hvA' : (vA : A) = (W.ΨSq n).eval xA := by
    rw [hvA, Units.coe_map, MonoidHom.coe_coe, hv, hΨ]
  have heq' : x * (vA : A) = (W.Φ n).eval xA := by rw [hvA']; exact heq
  rw [hinv, ← heq', Units.mul_inv_cancel_right]

include hp2 ha ha' heqP in

theorem xP_eq_classify_torusX : D'.xP = UnivBasisRing.classify p W (hpA.mul hW) D hD (torusX p a) :=
  eq_classify_mul_inverse p hpA W hW D hD _ a (isUnit_ΨSq_univP p hp2 ha ha')
    (congrArg LevelPData.xP (univData_map_classify p W (hpA.mul hW) D hD)) heqP

include hp2 hb hb' heqQ in

theorem xQ_eq_classify_borelX : D'.xQ = UnivBasisRing.classify p W (hpA.mul hW) D hD (borelX p b) :=
  eq_classify_mul_inverse p hpA W hW D hD _ b (isUnit_ΨSq_univQ p hp2 hb hb')
    (congrArg LevelPData.xQ (univData_map_classify p W (hpA.mul hW) D hD)) heqQ

omit [Fact p.Prime] in
include hD' in

theorem isLevelPStructure_map_classify' : IsLevelPStructure ((univCurveT p).map (UnivBasisRing.classify p W (hpA.mul hW) D hD)) p D' := by
  rwa [univCurveT_map_classify]

def torusTheta : TorusRing p a b →+* A :=
  TorusRing.lift p a b (UnivBasisRing.classify p W (hpA.mul hW) D hD) D'
    (isLevelPStructure_map_classify' p hpA W hW D D' hD hD')
    (xP_eq_classify_torusX p hpA hp2 W hW D D' hD ha ha' heqP)
    (xQ_eq_classify_borelX p hpA hp2 W hW D D' hD hb hb' heqQ)

theorem torusTheta_comp_ofUniv :
    (torusTheta p hpA hp2 W hW D D' hD hD' ha ha' hb hb' heqP heqQ).comp (TorusRing.ofUniv p a b) =
    UnivBasisRing.classify p W (hpA.mul hW) D hD :=
  TorusRing.lift_comp_ofUniv p a b _ _ _ _ _

theorem torusTheta_comp_torusBeta :
    (torusTheta p hpA hp2 W hW D D' hD hD' ha ha' hb hb' heqP heqQ).comp (torusBeta p hp2 a b ha ha' hb hb') =
    UnivBasisRing.classify p W (hpA.mul hW) D' hD' := by
  refine UnivBasisRing.eq_classify p _ _ _ _ ?_ ?_
  · rw [← WeierstrassCurve.map_map, univCurveT_map_torusBeta, torusTheta, torusCurve_map_lift,
      univCurveT_map_classify]
  · rw [← LevelPData.map_map, univData_map_torusBeta, torusTheta, torusData'_map_lift]

theorem torus_eval (g : S ⊗[ℤ] UnivBasisRing p) :
    sClassify p S hpA W hW D' hD' g - sClassify p S hpA W hW D hD g =
      sLift S (torusTheta p hpA hp2 W hW D D' hD hD' ha ha' hb hb' heqP heqQ)
        (LinearMap.lTensor S (torusForm p hp2 a b ha ha' hb hb') g) := by
  rw [sLift_lTensor p S hpA (torusBeta p hp2 a b ha ha' hb hb') (TorusRing.ofUniv p a b) 1
    (torusForm p hp2 a b ha ha' hb hb') (fun t => by rw [torusForm_apply, one_mul]) _ W hW D hD W hW D' hD'
    (torusTheta_comp_ofUniv p hpA hp2 W hW D D' hD hD' ha ha' hb hb' heqP heqQ)
    (torusTheta_comp_torusBeta p hpA hp2 W hW D D' hD hD' ha ha' hb hb' heqP heqQ) g, map_one, one_mul]

end TorusTarget

end Targets

section FormOf

variable (p : ℕ) (S : Type u) [CommRing S] (hpS : IsUnit (p : S)) (k : ℤ)

include hpS in
theorem isUnit_natCast_algebra (A : Type u) [CommRing A] [Algebra S A] : IsUnit (p : A) := by
  simpa only [map_natCast] using hpS.map (algebraMap S A)

variable (g : S ⊗[ℤ] UnivBasisRing p) (hg : LinearMap.lTensor S (vcForm p k) g = 0)

def formOf : KatzLevelPForm S p k where
  toFun A _ _ W hW D hD := sClassify p S (isUnit_natCast_algebra p S hpS A) W hW D hD g
  map_toFun A B _ _ _ _ f W hW hW' D hD hD' := by
    show sClassify p S _ _ hW' _ hD' g = f (sClassify p S _ W hW D hD g)
    rw [← AlgHom.comp_apply, comp_sClassify p S _ W hW D hD f (isUnit_natCast_algebra p S hpS B) hW' hD']
  toFun_variableChange A _ _ C W hW hW' D hD hD' := by
    have h := vc_eval p S (isUnit_natCast_algebra p S hpS A) W hW D hD C hW' hD' k g
    rw [hg, map_zero, sub_eq_zero] at h
    exact h

theorem formOf_toFun {A : Type u} [CommRing A] [Algebra S A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
    (D : LevelPData A) (hD : IsLevelPStructure W p D) :
    (formOf p S hpS k g hg).toFun W hW D hD = sClassify p S (isUnit_natCast_algebra p S hpS A) W hW D hD g := rfl

variable [Fact p.Prime] (hp2 : p ≠ 2)

include hp2 in

theorem dependsOnlyOnLines_formOf
    (ht : ∀ (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2),
      LinearMap.lTensor S (torusForm p hp2 a b ha ha' hb hb') g = 0) :
    (formOf p S hpS k g hg).DependsOnlyOnLines := by
  intro A _ _ W hW D D' hD hD' hinP hinQ
  obtain ⟨a, ha, ha', heqP⟩ := hinP
  obtain ⟨b, hb, hb', heqQ⟩ := hinQ
  have h := torus_eval p S (isUnit_natCast_algebra p S hpS A) hp2 W hW D D' hD hD' ha ha' hb hb' heqP heqQ g
  rw [ht a b ha ha' hb hb', map_zero, sub_eq_zero] at h
  exact h

omit [Fact p.Prime] in

theorem formOf_toFun_univ :
    (formOf p S hpS k g hg).toFun (KatzLevelPForm.univCurveOver S p) (KatzLevelPForm.isUnit_Δ_univCurveOver S p)
      (KatzLevelPForm.univDataOver S p) (KatzLevelPForm.isLevelPStructure_univDataOver S p) = g := by
  rw [formOf_toFun, sClassify_self]
  rfl

end FormOf

section RingSide

variable (p : ℕ) {R : Type u} [CommRing R] (hpR : IsUnit (p : R)) {k : ℤ} (G : KatzLevelPForm R p k)

theorem sLift_includeRight {N : Type} [CommRing N] :
    sLift R ((Algebra.TensorProduct.includeRight : N →ₐ[ℤ] R ⊗[ℤ] N) : N →+* R ⊗[ℤ] N) = AlgHom.id R _ := by
  refine Algebra.TensorProduct.ext' fun s n => ?_
  rw [sLift_tmul, AlgHom.id_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  show (s ⊗ₜ[ℤ] (1 : N)) * ((1 : R) ⊗ₜ[ℤ] n) = s ⊗ₜ[ℤ] n
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

include hpR in

theorem lTensor_vcForm_evalUniv : LinearMap.lTensor R (vcForm p k) G.evalUniv = 0 := by
  let incl : VCRing p →+* R ⊗[ℤ] VCRing p :=
    (Algebra.TensorProduct.includeRight : VCRing p →ₐ[ℤ] R ⊗[ℤ] VCRing p)
  have hpA : IsUnit (p : R ⊗[ℤ] VCRing p) := isUnit_natCast_algebra p R hpR _
  let W₁ : WeierstrassCurve (R ⊗[ℤ] VCRing p) := (vcCurve p).map incl
  let D₁ : LevelPData (R ⊗[ℤ] VCRing p) := (vcData p).map incl
  have hW₁ : IsUnit W₁.Δ := KatzModularForm.isUnit_Δ_map _ (isUnit_Δ_vcCurve p)
  have hD₁ : IsLevelPStructure W₁ p D₁ := (isLevelPStructure_vcData p).map incl
  let C₁ : VariableChange (R ⊗[ℤ] VCRing p) := (univVC p).map incl
  have hW₁' : IsUnit (C₁ • W₁).Δ := by
    rw [variableChange_Δ]; exact ((Units.isUnit _).pow 12).mul hW₁
  have hD₁' : IsLevelPStructure (C₁ • W₁) p (D₁.variableChange C₁) :=
    hD₁.variableChange C₁

  have hcl : incl.comp (VCRing.ofUniv p) = UnivBasisRing.classify p W₁ (hpA.mul hW₁) D₁ hD₁ :=
    UnivBasisRing.eq_classify p _ _ _ _ (by rw [← WeierstrassCurve.map_map]; rfl)
      (by rw [← LevelPData.map_map]; rfl)
  have hθ : vcTheta p hpA W₁ hW₁ D₁ hD₁ C₁ = incl := by
    refine VCRing.ringHom_ext p ?_ ?_
    · rw [vcTheta_comp_ofUniv, hcl]
    · intro i
      rw [vcTheta, VCRing.lift_vcVar]
      fin_cases i <;> rfl
  have h := vc_eval p R hpA W₁ hW₁ D₁ hD₁ C₁ hW₁' hD₁' k G.evalUniv
  rw [hθ, sLift_includeRight, AlgHom.id_apply, ← toFun_eq_sClassify_evalUniv,
    ← toFun_eq_sClassify_evalUniv, G.toFun_variableChange C₁ W₁ hW₁ hW₁' D₁ hD₁ hD₁', sub_self] at h
  exact h.symm

variable [Fact p.Prime] (hp2 : p ≠ 2)

omit [Fact p.Prime] in
theorem eval_ΨSq_map {T T' : Type*} [CommRing T] [CommRing T'] (ψ : T →+* T') (W : WeierstrassCurve T)
    (n : ℤ) (x : T) : ((W.map ψ).ΨSq n).eval (ψ x) = ψ ((W.ΨSq n).eval x) := by
  rw [WeierstrassCurve.map_ΨSq, Polynomial.eval_map, Polynomial.eval₂_at_apply]

omit [Fact p.Prime] in
theorem eval_Φ_map {T T' : Type*} [CommRing T] [CommRing T'] (ψ : T →+* T') (W : WeierstrassCurve T)
    (n : ℤ) (x : T) : ((W.map ψ).Φ n).eval (ψ x) = ψ ((W.Φ n).eval x) := by
  rw [WeierstrassCurve.map_Φ, Polynomial.eval_map, Polynomial.eval₂_at_apply]

include hp2 in

theorem torus_lineEqP₀ {a b : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) :
    (torusData' p a b).xP * ((torusCurve p a b).ΨSq a).eval (torusData p a b).xP =
      ((torusCurve p a b).Φ a).eval (torusData p a b).xP := by
  obtain ⟨v, hv⟩ := isUnit_ΨSq_univP p hp2 ha ha'
  have hxP' : (torusData' p a b).xP = TorusRing.ofUniv p a b (torusX p a) := torusData'_xP p a b
  have hxP : (torusData p a b).xP = TorusRing.ofUniv p a b (univData p).xP := rfl
  rw [hxP', hxP, torusCurve, eval_ΨSq_map, eval_Φ_map, ← map_mul, torusX, mul_assoc, ← hv,
    Ring.inverse_unit, Units.inv_mul, mul_one]

include hp2 in
theorem torus_lineEqQ₀ {a b : ℕ} (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2) :
    (torusData' p a b).xQ * ((torusCurve p a b).ΨSq b).eval (torusData p a b).xQ =
      ((torusCurve p a b).Φ b).eval (torusData p a b).xQ := by
  obtain ⟨v, hv⟩ := isUnit_ΨSq_univQ p hp2 hb hb'
  have hxQ' : (torusData' p a b).xQ = TorusRing.ofUniv p a b (borelX p b) := torusData'_xQ p a b
  have hxQ : (torusData p a b).xQ = TorusRing.ofUniv p a b (univData p).xQ := rfl
  rw [hxQ', hxQ, torusCurve, eval_ΨSq_map, eval_Φ_map, ← map_mul, borelX, mul_assoc, ← hv,
    Ring.inverse_unit, Units.inv_mul, mul_one]

include hpR hp2 in

theorem lTensor_torusForm_evalUniv (hG : G.DependsOnlyOnLines) {a b : ℕ} (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2)
    (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2) :
    LinearMap.lTensor R (torusForm p hp2 a b ha ha' hb hb') G.evalUniv = 0 := by
  let incl : TorusRing p a b →+* R ⊗[ℤ] TorusRing p a b :=
    (Algebra.TensorProduct.includeRight : TorusRing p a b →ₐ[ℤ] R ⊗[ℤ] TorusRing p a b)
  have hpA : IsUnit (p : R ⊗[ℤ] TorusRing p a b) := isUnit_natCast_algebra p R hpR _
  let W₁ : WeierstrassCurve (R ⊗[ℤ] TorusRing p a b) := (torusCurve p a b).map incl
  let D₁ : LevelPData (R ⊗[ℤ] TorusRing p a b) := (torusData p a b).map incl
  let D₁' : LevelPData (R ⊗[ℤ] TorusRing p a b) := (torusData' p a b).map incl
  have hW₁ : IsUnit W₁.Δ := KatzModularForm.isUnit_Δ_map _ (isUnit_Δ_torusCurve p a b)
  have hD₁ : IsLevelPStructure W₁ p D₁ := (isLevelPStructure_torusData p a b).map incl
  have hD₁' : IsLevelPStructure W₁ p D₁' := (isLevelPStructure_torusData' p hp2 ha ha' hb hb').map incl
  have heqP : D₁'.xP * (W₁.ΨSq a).eval D₁.xP = (W₁.Φ a).eval D₁.xP := by
    show incl (torusData' p a b).xP * (((torusCurve p a b).map incl).ΨSq a).eval (incl (torusData p a b).xP) =
      (((torusCurve p a b).map incl).Φ a).eval (incl (torusData p a b).xP)
    rw [eval_ΨSq_map, eval_Φ_map, ← map_mul, torus_lineEqP₀ p hp2 ha ha']
  have heqQ : D₁'.xQ * (W₁.ΨSq b).eval D₁.xQ = (W₁.Φ b).eval D₁.xQ := by
    show incl (torusData' p a b).xQ * (((torusCurve p a b).map incl).ΨSq b).eval (incl (torusData p a b).xQ) =
      (((torusCurve p a b).map incl).Φ b).eval (incl (torusData p a b).xQ)
    rw [eval_ΨSq_map, eval_Φ_map, ← map_mul, torus_lineEqQ₀ p hp2 hb hb']
  have hcl : incl.comp (TorusRing.ofUniv p a b) = UnivBasisRing.classify p W₁ (hpA.mul hW₁) D₁ hD₁ :=
    UnivBasisRing.eq_classify p _ _ _ _ (by rw [← WeierstrassCurve.map_map]; rfl)
      (by rw [← LevelPData.map_map]; rfl)
  have hθ : torusTheta p hpA hp2 W₁ hW₁ D₁ D₁' hD₁ hD₁' ha ha' hb hb' heqP heqQ = incl := by
    refine TorusRing.ringHom_ext p a b ?_ ?_
    · rw [torusTheta_comp_ofUniv, hcl]
    · rw [torusTheta, torusData'_map_lift]
  have h := torus_eval p R hpA hp2 W₁ hW₁ D₁ D₁' hD₁ hD₁' ha ha' hb hb' heqP heqQ G.evalUniv
  rw [hθ, sLift_includeRight, AlgHom.id_apply, ← toFun_eq_sClassify_evalUniv,
    ← toFun_eq_sClassify_evalUniv, hG W₁ hW₁ D₁ D₁' hD₁ hD₁' ⟨a, ha, ha', heqP⟩ ⟨b, hb, hb', heqQ⟩,
    sub_self] at h
  exact h.symm

end RingSide

section Descent

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := fun x y h =>
  HahnSeries.ext (funext fun k => hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h]))

theorem isLevelPStructure_of_map {A A' : Type u} [CommRing A] [CommRing A'] {φ : A →+* A'}
    (hφ : Function.Injective φ) {W : WeierstrassCurve A} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : IsUnit (p : A)) (hΔ : IsUnit W.Δ) {D : LevelPData A}
    (h : IsLevelPStructure (W.map φ) p (D.map φ)) (hPQ : IsUnit (indepElt W p D.xP D.xQ)) :
    IsLevelPStructure W p D := by
  have hP : W.toAffine.Equation D.xP D.yP :=
    (WeierstrassCurve.Affine.map_equation (W := W.toAffine) hφ _ _).mp h.equation_P
  have hQ : W.toAffine.Equation D.xQ D.yQ :=
    (WeierstrassCurve.Affine.map_equation (W := W.toAffine) hφ _ _).mp h.equation_Q
  have hψP : (W.preΨ p).eval D.xP = 0 := hφ (by
    have h1 := h.preΨ_P
    rw [LevelPData.map_xP, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply] at h1
    rw [h1, map_zero])
  have hψQ : (W.preΨ p).eval D.xQ = 0 := hφ (by
    have h1 := h.preΨ_Q
    rw [LevelPData.map_xQ, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply] at h1
    rw [h1, map_zero])
  exact ⟨hP, hQ, hψP, hψQ, hPQ, isUnit_indepElt_symm W p hp2 hp hΔ hP hQ hψP hψQ hPQ⟩

theorem isUnit_natCast_laurentSeries {B : Type*} [CommRing B] {p : ℕ} (hpB : IsUnit (p : B)) :
    IsUnit (p : LaurentSeries B) := by
  simpa only [map_natCast] using hpB.map (algebraMap B (LaurentSeries B))

theorem tateBase_map_coeffMap (p : ℕ) [Fact p.Prime] {B S : Type*} [CommRing B] [CommRing S]
    (f : B →+* S) : (tateBase B p).map (coeffMap f) = tateBase S p := by
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [tateBase, WeierstrassCurve.map_map]
  have hc : (coeffMap f).comp (qExpand B p) = (qExpand S p).comp (coeffMap f) :=
    RingHom.ext fun x => coeffMap_qExpand f p x
  rw [hc, ← WeierstrassCurve.map_map, map_coeffMap_tateLaurent, tateBase]

theorem cuspLevel_of_injective {B R : Type u} [CommRing B] [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpB : IsUnit (p : B)) (ζ : Bˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : B) ^ i = 0)
    (f : B →+* R) (hf : Function.Injective f) (v w : Fin 2 → ZMod p)
    (hc : IsLevelPStructure (tateBase R p) p (cuspData R p (Units.map (f : B →* R) ζ) v w))
    (hPQ : IsUnit (indepElt (tateBase B p) p (cuspData B p ζ v w).xP (cuspData B p ζ v w).xQ)) :
    IsLevelPStructure (tateBase B p) p (cuspData B p ζ v w) := by
  have hprime : p.Prime := Fact.out
  haveI : NeZero p := ⟨hprime.ne_zero⟩
  refine isLevelPStructure_of_map (coeffMap_injective hf) hp2 (isUnit_natCast_laurentSeries hpB)
    (isUnit_Δ_tateBase B p) ?_ hPQ
  rw [tateBase_map_coeffMap p f, cuspData_map_coeffMap f p hpB ζ hζ]
  exact hc

theorem cuspLevel_map {B S : Type u} [CommRing B] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hpB : IsUnit (p : B)) (ζ : Bˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : B) ^ i = 0) (f : B →+* S)
    (v w : Fin 2 → ZMod p) (hcB : IsLevelPStructure (tateBase B p) p (cuspData B p ζ v w)) :
    IsLevelPStructure (tateBase S p) p (cuspData S p (Units.map (f : B →* S) ζ) v w) := by
  have h := hcB.map (coeffMap f)
  rwa [tateBase_map_coeffMap p f, cuspData_map_coeffMap f p hpB ζ hζ] at h

theorem coeffMap_indepElt_cuspData {B S : Type u} [CommRing B] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hpB : IsUnit (p : B)) (ζ : Bˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : B) ^ i = 0) (f : B →+* S)
    (v w : Fin 2 → ZMod p) :
    coeffMap f (indepElt (tateBase B p) p (cuspData B p ζ v w).xP (cuspData B p ζ v w).xQ) =
      indepElt (tateBase S p) p (cuspData S p (Units.map (f : B →* S) ζ) v w).xP
        (cuspData S p (Units.map (f : B →* S) ζ) v w).xQ := by
  rw [← indepElt_map, tateBase_map_coeffMap p f, ← LevelPData.map_xP, ← LevelPData.map_xQ,
    cuspData_map_coeffMap f p hpB ζ hζ]

theorem exists_fg_isUnit_indepElt {B R : Type u} [CommRing B] [CommRing R] [Algebra B R] (p : ℕ)
    [Fact p.Prime] (hpB : IsUnit (p : B)) (ζ : Bˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : B) ^ i = 0)
    (v w : Fin 2 → ZMod p)
    (hc : IsLevelPStructure (tateBase R p) p
      (cuspData R p (Units.map (algebraMap B R : B →* R) ζ) v w)) :
    ∃ B₁ : Subalgebra B R, B₁.FG ∧
      IsUnit (indepElt (tateBase B₁ p) p
        (cuspData B₁ p (Units.map (algebraMap B B₁ : B →* B₁) ζ) v w).xP
        (cuspData B₁ p (Units.map (algebraMap B B₁ : B →* B₁) ζ) v w).xQ) := by
  set x := indepElt (tateBase B p) p (cuspData B p ζ v w).xP (cuspData B p ζ v w).xQ with hx
  have hxR : IsUnit (x.map (algebraMap B R)) := by
    have h := coeffMap_indepElt_cuspData p hpB ζ hζ (algebraMap B R) v w
    rw [← hx] at h
    show IsUnit (coeffMap (algebraMap B R) x)
    rw [h]
    exact hc.isUnit_indepElt_PQ
  obtain ⟨B₁, hfg, hu⟩ := LaurentSeries.exists_fg_subalgebra_isUnit_map_of_isUnit_map x hxR
  refine ⟨B₁, hfg, ?_⟩
  have h := coeffMap_indepElt_cuspData p hpB ζ hζ (algebraMap B B₁) v w
  rw [← hx] at h
  rw [← h]
  exact hu

end Descent

section QExp

variable (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (B : Type u) [CommRing B] (hpB : IsUnit (p : B)) (ζ : Bˣ)
  (hζ : ∑ i ∈ Finset.range p, (ζ : B) ^ i = 0)
  (hcB : IsLevelPStructure (tateBase B p) p (cuspData B p ζ ![0, 1] ![1, 1]))

def qAlg : B ⊗[ℤ] UnivBasisRing p →ₐ[B] LaurentSeries B :=
  sClassify p B (isUnit_natCast_algebra p B hpB (LaurentSeries B)) (tateBase B p) (isUnit_Δ_tateBase B p)
    (cuspData B p ζ ![0, 1] ![1, 1]) hcB

theorem coeff_C_mul {S : Type*} [CommRing S] (b : S) (z : LaurentSeries S) (n : ℤ) :
    (HahnSeries.C b * z).coeff n = b * z.coeff n := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

def qForm (n : ℤ) : B ⊗[ℤ] UnivBasisRing p →ₗ[B] B where
  toFun y := (qAlg p B hpB ζ hcB y).coeff n
  map_add' x y := by rw [map_add, HahnSeries.coeff_add]
  map_smul' b y := by
    show (qAlg p B hpB ζ hcB (b • y)).coeff n = b * (qAlg p B hpB ζ hcB y).coeff n
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, HahnSeries.coeff_zero, mul_zero]
    | tmul b' t =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, qAlg, sClassify_tmul, sClassify_tmul, algebraMap_laurentSeries_apply,
        algebraMap_laurentSeries_apply, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, coeff_C_mul,
        coeff_C_mul, mul_assoc]
    | add x y hx hy => rw [smul_add, map_add, HahnSeries.coeff_add, hx, hy, map_add, HahnSeries.coeff_add, mul_add]

theorem qForm_apply (n : ℤ) (y : B ⊗[ℤ] UnivBasisRing p) :
    qForm p B hpB ζ hcB n y = (qAlg p B hpB ζ hcB y).coeff n := rfl

variable (S : Type u) [CommRing S] [Algebra B S] (ζ' : Sˣ) (hζ' : Units.map (algebraMap B S : B →* S) ζ = ζ')
  (hc' : IsLevelPStructure (tateBase S p) p (cuspData S p ζ' ![0, 1] ![1, 1])) (hpS' : IsUnit (p : LaurentSeries S))

include hζ hζ' in

theorem coeffMap_comp_classify :
    (coeffMap (algebraMap B S)).comp
      (UnivBasisRing.classify p (tateBase B p)
        ((isUnit_natCast_algebra p B hpB (LaurentSeries B)).mul (isUnit_Δ_tateBase B p))
        (cuspData B p ζ ![0, 1] ![1, 1]) hcB) =
      UnivBasisRing.classify p (tateBase S p) (hpS'.mul (isUnit_Δ_tateBase S p)) (cuspData S p ζ' ![0, 1] ![1, 1]) hc' := by
  refine UnivBasisRing.eq_classify p _ _ _ _ ?_ ?_
  · rw [← WeierstrassCurve.map_map, univCurveT_map_classify, tateBase_map_coeffMap]
  · rw [← LevelPData.map_map, univData_map_classify, cuspData_map_coeffMap _ p hpB ζ hζ, hζ']

abbrev cbc (T : Type) [AddCommGroup T] : S ⊗[B] (B ⊗[ℤ] T) ≃ₗ[B] S ⊗[ℤ] T :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ B B S T

omit [Fact p.Prime] in

theorem cbc_lTensor_baseChange {T Q : Type} [AddCommGroup T] [AddCommGroup Q] (f : T →ₗ[ℤ] Q)
    (x : S ⊗[B] (B ⊗[ℤ] T)) :
    cbc B S Q (LinearMap.lTensor S (f.baseChange B) x) = LinearMap.lTensor S f (cbc B S T x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | tmul s y =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [TensorProduct.tmul_zero, LinearMap.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero,
        LinearMap.map_zero]
    | tmul b t =>
      rw [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.lTensor_tmul]
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, LinearMap.map_add, LinearEquiv.map_add, hx, hy, LinearEquiv.map_add,
        LinearMap.map_add]
  | add x y hx hy =>
    rw [LinearMap.map_add, LinearEquiv.map_add, hx, hy, LinearEquiv.map_add, LinearMap.map_add]

include hζ hζ' in

theorem q_eval (x : S ⊗[B] (B ⊗[ℤ] UnivBasisRing p)) (n : ℤ) :
    (sClassify p S hpS' (tateBase S p) (isUnit_Δ_tateBase S p) (cuspData S p ζ' ![0, 1] ![1, 1]) hc'
        (cbc B S (UnivBasisRing p) x)).coeff n =
      TensorProduct.rid B S (LinearMap.lTensor S (qForm p B hpB ζ hcB n) x) := by
  have hnat := coeffMap_comp_classify p B hpB ζ hζ hcB S ζ' hζ' hc' hpS'
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [LinearEquiv.map_zero, map_zero, HahnSeries.coeff_zero, LinearMap.map_zero, LinearEquiv.map_zero]
  | tmul s y =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, HahnSeries.coeff_zero, LinearMap.map_zero,
        LinearEquiv.map_zero]
    | tmul b t =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, sClassify_tmul, ← hnat, RingHom.comp_apply,
        algebraMap_laurentSeries_apply, Algebra.algebraMap_self, RingHom.id_apply, coeff_C_mul, coeffMap_coeff,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul, qForm_apply, qAlg, sClassify_tmul,
        algebraMap_laurentSeries_apply, Algebra.algebraMap_self, RingHom.id_apply, coeff_C_mul,
        Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, LinearEquiv.map_add, map_add, HahnSeries.coeff_add, hx, hy, LinearMap.map_add,
        LinearEquiv.map_add]
  | add x y hx hy =>
    rw [LinearEquiv.map_add, map_add, HahnSeries.coeff_add, hx, hy, LinearMap.map_add, LinearEquiv.map_add]

end QExp

inductive Idx (p : ℕ) : Type
  | vc : Idx p
  | torus (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2) : Idx p
  | coeff (n : ℤ) : Idx p

section Flatness

variable (p : ℕ)

theorem flat_int_transfer {M : Type*} [AddCommGroup M] (i₁ i₂ : Module ℤ M)
    (h : @Module.Flat ℤ M _ _ i₁) : @Module.Flat ℤ M _ _ i₂ := by
  have e : i₁ = i₂ := Subsingleton.elim _ _
  subst e
  exact h

theorem flat_int_univBasisRing (i : Module ℤ (UnivBasisRing p)) : @Module.Flat ℤ (UnivBasisRing p) _ _ i :=
  flat_int_transfer _ _ (flat_univBasisRing_vcRing_borelRing p).1

theorem flat_int_of_flat (T : Type) [CommRing T] [Algebra (UnivBasisRing p) T]
    [hT : Module.Flat (UnivBasisRing p) T] (i : Module ℤ T) : @Module.Flat ℤ T _ _ i := by
  have h1 : (algebraMap ℤ (UnivBasisRing p)).Flat := RingHom.flat_algebraMap_iff.mpr (flat_int_univBasisRing p _)
  have h2 : (algebraMap (UnivBasisRing p) T).Flat := RingHom.flat_algebraMap_iff.mpr hT
  have h := RingHom.Flat.comp h1 h2
  have e : (algebraMap (UnivBasisRing p) T).comp (algebraMap ℤ (UnivBasisRing p)) = algebraMap ℤ T :=
    RingHom.ext_int _ _
  rw [e, RingHom.flat_algebraMap_iff] at h
  exact flat_int_transfer _ _ h

scoped instance flat_univBasisRing_int : Module.Flat ℤ (UnivBasisRing p) := flat_int_univBasisRing p _

scoped instance flat_vcRing_int : Module.Flat ℤ (VCRing p) := by
  haveI := (flat_univBasisRing_vcRing_borelRing p).2.1
  exact flat_int_of_flat p (VCRing p) _

theorem flat_torusRing (a b : ℕ) : Module.Flat (UnivBasisRing p) (TorusRing p a b) := by
  haveI : Module.Free (UnivBasisRing p) (BorelQRing p b) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_borelQuadratic p b)).basis
  haveI : Module.Free (BorelQRing p b) (TorusQRing p a b) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_torusQuadratic_map p a b)).basis
  haveI : Module.Flat (UnivBasisRing p) (TorusQRing p a b) :=
    Module.Flat.trans (UnivBasisRing p) (BorelQRing p b) (TorusQRing p a b)
  haveI : Module.Flat (TorusQRing p a b) (TorusRing p a b) :=
    IsLocalization.flat (TorusRing p a b) (Submonoid.powers (torusDenom p a b))
  exact Module.Flat.trans (UnivBasisRing p) (TorusQRing p a b) (TorusRing p a b)

scoped instance flat_torusRing_int (a b : ℕ) : Module.Flat ℤ (TorusRing p a b) := by
  haveI := flat_torusRing p a b
  exact flat_int_of_flat p (TorusRing p a b) _

variable (B : Type u) [CommRing B]

def N : Idx p → Type u
  | .vc => B ⊗[ℤ] VCRing p
  | .torus a b _ _ _ _ => B ⊗[ℤ] TorusRing p a b
  | .coeff _ => B

scoped instance instAddCommGroupN : ∀ j : Idx p, AddCommGroup (N p B j)
  | .vc => inferInstanceAs (AddCommGroup (B ⊗[ℤ] VCRing p))
  | .torus a b _ _ _ _ => inferInstanceAs (AddCommGroup (B ⊗[ℤ] TorusRing p a b))
  | .coeff _ => inferInstanceAs (AddCommGroup B)

scoped instance instModuleN : ∀ j : Idx p, Module B (N p B j)
  | .vc => inferInstanceAs (Module B (B ⊗[ℤ] VCRing p))
  | .torus a b _ _ _ _ => inferInstanceAs (Module B (B ⊗[ℤ] TorusRing p a b))
  | .coeff _ => inferInstanceAs (Module B B)

scoped instance instFlatN : ∀ j : Idx p, Module.Flat B (N p B j)
  | .vc => inferInstanceAs (Module.Flat B (B ⊗[ℤ] VCRing p))
  | .torus a b _ _ _ _ => inferInstanceAs (Module.Flat B (B ⊗[ℤ] TorusRing p a b))
  | .coeff _ => inferInstanceAs (Module.Flat B B)

end Flatness

section Devissage

variable (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (k : ℤ) (B : Type u) [CommRing B] (hpB : IsUnit (p : B)) (ζ : Bˣ)
  (hζ : ∑ i ∈ Finset.range p, (ζ : B) ^ i = 0)
  (hcB : IsLevelPStructure (tateBase B p) p (cuspData B p ζ ![0, 1] ![1, 1]))

def fam : ∀ j : Idx p, (B ⊗[ℤ] UnivBasisRing p) →ₗ[B] N p B j
  | .vc => (vcForm p k).baseChange B
  | .torus a b ha ha' hb hb' => (torusForm p hp2 a b ha ha' hb hb').baseChange B
  | .coeff n => qForm p B hpB ζ hcB n

include hζ in

theorem field_step (K : Type u) [Field K] [Algebra B K]
    (hF : ∀ (ξ : Kˣ), ∑ i ∈ Finset.range p, (ξ : K) ^ i = 0 →
      ∀ (hcK : IsLevelPStructure (tateBase K p) p (cuspData K p ξ ![0, 1] ![1, 1]))
      (H : KatzLevelPForm K p k), H.DependsOnlyOnLines →
      H.toFun (tateBase K p) (isUnit_Δ_tateBase K p) _ hcK = 0 → H = 0)
    (x : K ⊗[B] (B ⊗[ℤ] UnivBasisRing p)) (hx : ∀ j, LinearMap.lTensor K (fam p hp2 k B hpB ζ hcB j) x = 0) :
    x = 0 := by
  have hpK : IsUnit (p : K) := isUnit_natCast_algebra p B hpB K
  let ξ : Kˣ := Units.map (algebraMap B K : B →* K) ζ
  have hξ : ∑ i ∈ Finset.range p, (ξ : K) ^ i = 0 := by
    have h := congrArg (algebraMap B K) hζ
    rw [map_sum, map_zero] at h
    simp only [map_pow] at h
    exact h
  have hcK : IsLevelPStructure (tateBase K p) p (cuspData K p ξ ![0, 1] ![1, 1]) :=
    cuspLevel_map p hpB ζ hζ (algebraMap B K) _ _ hcB
  set g := cbc B K (UnivBasisRing p) x with hg
  have hvc : LinearMap.lTensor K (vcForm p k) g = 0 := by
    rw [hg, ← cbc_lTensor_baseChange]
    exact (congrArg (cbc B K (VCRing p)) (hx .vc)).trans (LinearEquiv.map_zero _)
  have ht : ∀ (a b : ℕ) (ha : 1 ≤ a) (ha' : a ≤ (p - 1) / 2) (hb : 1 ≤ b) (hb' : b ≤ (p - 1) / 2),
      LinearMap.lTensor K (torusForm p hp2 a b ha ha' hb hb') g = 0 := by
    intro a b ha ha' hb hb'
    rw [hg, ← cbc_lTensor_baseChange]
    exact (congrArg (cbc B K (TorusRing p a b)) (hx (.torus a b ha ha' hb hb'))).trans (LinearEquiv.map_zero _)
  have hdep := dependsOnlyOnLines_formOf p K hpK k g hvc hp2 ht
  have hq : (formOf p K hpK k g hvc).toFun (tateBase K p) (isUnit_Δ_tateBase K p) _ hcK = 0 := by
    rw [formOf_toFun]
    refine HahnSeries.ext (funext fun n => ?_)
    have hxn : LinearMap.lTensor K (qForm p B hpB ζ hcB n) x = 0 := hx (.coeff n)
    rw [q_eval p B hpB ζ hζ hcB K ξ rfl hcK (isUnit_natCast_algebra p K hpK (LaurentSeries K)) x n,
      hxn, LinearEquiv.map_zero, HahnSeries.coeff_zero]
  have hH := hF ξ hξ hcK (formOf p K hpK k g hvc) hdep hq
  have hg0 : g = 0 := by
    rw [← formOf_toFun_univ p K hpK k g hvc, hH]
    rfl
  exact (cbc B K (UnivBasisRing p)).injective (hg0.trans (LinearEquiv.map_zero _).symm)

theorem exists_fg_rTensor_eq (R : Type u) [CommRing R] [Algebra B R] {T : Type u} [AddCommGroup T] [Module B T]
    (x : R ⊗[B] T) :
    ∃ (M : Submodule B R) (_ : Module.Finite B M) (y : M ⊗[B] T), LinearMap.rTensor T M.subtype y = x := by
  classical
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset x
  let M : Submodule B R := Submodule.span B (s.image Prod.fst : Set R)
  have hmem : ∀ i ∈ s, i.1 ∈ M := fun i hi =>
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst hi))
  refine ⟨M, Module.Finite.span_of_finite B (Finset.finite_toSet _),
    ∑ i ∈ s.attach, (⟨i.1.1, hmem i.1 i.2⟩ : M) ⊗ₜ i.1.2, ?_⟩
  rw [map_sum]
  simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
  exact Finset.sum_attach s (fun i => i.1 ⊗ₜ[B] i.2)

end Devissage

section Main

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))
  (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) {k : ℤ}
  (hc : IsLevelPStructure (tateBase R p) p (cuspData R p ζ ![0, 1] ![1, 1]))
  (G : KatzLevelPForm R p k) (hG : G.DependsOnlyOnLines)
  (h0 : G.toFun (tateBase R p) (isUnit_Δ_tateBase R p) _ hc = 0)
  (hF : ∀ (K : Type u) [Field K], (p : K) ≠ 0 → ∀ (ξ : Kˣ),
    ∑ i ∈ Finset.range p, (ξ : K) ^ i = 0 →
    ∀ (hcK : IsLevelPStructure (tateBase K p) p (cuspData K p ξ ![0, 1] ![1, 1]))
    (H : KatzLevelPForm K p k), H.DependsOnlyOnLines →
    H.toFun (tateBase K p) (isUnit_Δ_tateBase K p) _ hcK = 0 → H = 0)

include hp2 hp hζ hG h0 hF in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main : G = 0 := by
  classical

  let s : Finset R := {(ζ : R), ((ζ⁻¹ : Rˣ) : R), ((hp.unit⁻¹ : Rˣ) : R)}
  let B₀ : Subalgebra ℤ R := Algebra.adjoin ℤ (s : Set R)
  haveI : IsNoetherianRing B₀ := isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset s)
  have hmem : ∀ x ∈ s, x ∈ B₀ := fun x hx => Algebra.subset_adjoin hx
  have h1 : (ζ : R) ∈ B₀ := hmem _ (by simp [s])
  have h2 : ((ζ⁻¹ : Rˣ) : R) ∈ B₀ := hmem _ (by simp [s])
  have h3 : ((hp.unit⁻¹ : Rˣ) : R) ∈ B₀ := hmem _ (by simp [s])
  let ζ₀ : B₀ˣ := ⟨⟨ζ, h1⟩, ⟨_, h2⟩, Subtype.ext ζ.mul_inv, Subtype.ext ζ.inv_mul⟩
  have hp₀ : IsUnit (p : B₀) := by
    refine ⟨⟨p, ⟨_, h3⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · show ((p : B₀) : R) * ((hp.unit⁻¹ : Rˣ) : R) = 1
      rw [show ((p : B₀) : R) = p by simp]; exact hp.mul_val_inv
    · show ((hp.unit⁻¹ : Rˣ) : R) * ((p : B₀) : R) = 1
      rw [show ((p : B₀) : R) = p by simp]; exact hp.val_inv_mul
  have hζ₀ : ∑ i ∈ Finset.range p, (ζ₀ : B₀) ^ i = 0 := by
    apply Subtype.val_injective
    push_cast
    exact hζ
  have hζmap : Units.map (algebraMap B₀ R : B₀ →* R) ζ₀ = ζ := Units.ext rfl

  obtain ⟨B₁, hB₁fg, hu₁⟩ := exists_fg_isUnit_indepElt (B := B₀) (R := R) p hp₀ ζ₀ hζ₀ ![0, 1] ![1, 1]
    (by rw [hζmap]; exact hc)
  haveI : Algebra.FiniteType B₀ B₁ := B₁.fg_iff_finiteType.mp hB₁fg
  haveI : IsNoetherianRing B₁ := Algebra.FiniteType.isNoetherianRing B₀ B₁
  have hp₁ : IsUnit (p : B₁) := by simpa only [map_natCast] using hp₀.map (algebraMap B₀ B₁)
  let ζ₁ : B₁ˣ := Units.map (algebraMap B₀ B₁ : B₀ →* B₁) ζ₀
  have hζ₁ : ∑ i ∈ Finset.range p, (ζ₁ : B₁) ^ i = 0 := by
    have h := congrArg (algebraMap B₀ B₁) hζ₀
    rw [map_sum, map_zero] at h
    simp only [map_pow] at h
    exact h
  have hζmap₁ : Units.map (algebraMap B₁ R : B₁ →* R) ζ₁ = ζ := Units.ext rfl

  have hc₁ : IsLevelPStructure (tateBase B₁ p) p (cuspData B₁ p ζ₁ ![0, 1] ![1, 1]) :=
    cuspLevel_of_injective p hp2 hp₁ ζ₁ hζ₁ (algebraMap B₁ R) Subtype.val_injective _ _
      (hζmap₁ ▸ hc) hu₁

  let e := cbc B₁ R (UnivBasisRing p)
  let x : R ⊗[B₁] (B₁ ⊗[ℤ] UnivBasisRing p) := e.symm G.evalUniv
  have hex : e x = G.evalUniv := e.apply_symm_apply _
  have hx : ∀ j, LinearMap.lTensor R (fam p hp2 k B₁ hp₁ ζ₁ hc₁ j) x = 0 := by
    intro j
    cases j with
    | vc =>
      show LinearMap.lTensor R ((vcForm p k).baseChange B₁) x = 0
      apply (cbc B₁ R (VCRing p)).injective
      refine (cbc_lTensor_baseChange B₁ R (vcForm p k) x).trans ?_
      show LinearMap.lTensor R (vcForm p k) (e x) = _
      rw [hex, lTensor_vcForm_evalUniv p hp G, LinearEquiv.map_zero]
    | torus a b ha ha' hb hb' =>
      show LinearMap.lTensor R ((torusForm p hp2 a b ha ha' hb hb').baseChange B₁) x = 0
      apply (cbc B₁ R (TorusRing p a b)).injective
      refine (cbc_lTensor_baseChange B₁ R (torusForm p hp2 a b ha ha' hb hb') x).trans ?_
      show LinearMap.lTensor R (torusForm p hp2 a b ha ha' hb hb') (e x) = _
      rw [hex, lTensor_torusForm_evalUniv p hp G hp2 hG ha ha' hb hb', LinearEquiv.map_zero]
    | coeff n =>
      show LinearMap.lTensor R (qForm p B₁ hp₁ ζ₁ hc₁ n) x = 0
      apply (TensorProduct.rid B₁ R).injective
      rw [LinearEquiv.map_zero, ← q_eval p B₁ hp₁ ζ₁ hζ₁ hc₁ R ζ hζmap₁ hc
        (isUnit_natCast_algebra p R hp (LaurentSeries R)) x n]
      show (sClassify p R _ (tateBase R p) (isUnit_Δ_tateBase R p) _ hc (e x)).coeff n = 0
      rw [hex, ← toFun_eq_sClassify_evalUniv p R _ (tateBase R p) (isUnit_Δ_tateBase R p) _ hc G, h0,
        HahnSeries.coeff_zero]

  obtain ⟨M, hM, y, hy⟩ := exists_fg_rTensor_eq B₁ R x
  haveI := hM
  have hy0 : ∀ j, LinearMap.lTensor M (fam p hp2 k B₁ hp₁ ζ₁ hc₁ j) y = 0 := by
    intro j
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := N p B₁ j) M.subtype M.injective_subtype
    have hcomm := LinearMap.congr_fun ((LinearMap.rTensor_comp_lTensor M M.subtype (fam p hp2 k B₁ hp₁ ζ₁ hc₁ j)).trans
      (LinearMap.lTensor_comp_rTensor M M.subtype (fam p hp2 k B₁ hp₁ ζ₁ hc₁ j)).symm) y
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
    rw [hcomm, hy, hx j, LinearMap.map_zero]

  have key := TensorProduct.eq_zero_of_forall_lTensor_eq_zero_of_field (fam p hp2 k B₁ hp₁ ζ₁ hc₁)
    (fun K _ _ g hg => field_step p hp2 k B₁ hp₁ ζ₁ hζ₁ hc₁ K
      (fun ξ hξ hcK H hH hq => hF K (isUnit_natCast_algebra p B₁ hp₁ K).ne_zero ξ hξ hcK H hH hq) g hg) y hy0
  have hx0 : x = 0 := by rw [← hy, key, LinearMap.map_zero]
  have hev : G.evalUniv = 0 := by rw [← hex, hx0, LinearEquiv.map_zero]
  refine KatzLevelPForm.ext fun A _ _ W hW D hD => ?_
  rw [toFun_eq_sClassify_evalUniv p R (isUnit_natCast_algebra p R hp A) W hW D hD G, hev, map_zero,
    KatzLevelPForm.zero_toFun]

end Main

end ModularCurve.QExpSplitDevissage
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.ModularCurve.QExpSplitDevissage"
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.ModularCurve"

theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p
      (ModularCurve.cuspData R p ζ ![0, 1] ![1, 1]))
    (G : ModularCurve.KatzLevelPForm R p k) (hG : G.DependsOnlyOnLines)
    (h0 : G.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ hc = 0)
    (hF : ∀ (K : Type u) [Field K], (p : K) ≠ 0 → ∀ (ξ : Kˣ),
      ∑ i ∈ Finset.range p, (ξ : K) ^ i = 0 →
      ∀ (hcK : ModularCurve.IsLevelPStructure (ModularCurve.tateBase K p) p
        (ModularCurve.cuspData K p ξ ![0, 1] ![1, 1]))
      (H : ModularCurve.KatzLevelPForm K p k), H.DependsOnlyOnLines →
      H.toFun (ModularCurve.tateBase K p) (ModularCurve.isUnit_Δ_tateBase K p) _ hcK = 0 → H = 0) :
    G = 0 :=
  ModularCurve.QExpSplitDevissage.main hp2 hp ζ hζ hc G hG h0 hF

end
end S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
end P2MW
export P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field (solution)
