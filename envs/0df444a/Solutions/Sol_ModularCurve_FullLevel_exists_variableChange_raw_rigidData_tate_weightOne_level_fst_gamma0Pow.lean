-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/086bc14c-d77d-5bf9-a187-f7a782aed8b5

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
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom
import Theorems.Thm_ModularCurve_exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
import Theorems.Thm_ModularCurve_FullLevel_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
import Theorems.Thm_ModularCurve_j_tateLaurent
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_neg_of_dvd
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

namespace TPAux

p2m_open "ModularCurve WeierstrassCurve~cusp"
open scoped Classical

theorem isLevelPStructure_of_map {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {p : ℕ} {D : ModularCurve.LevelPData K}
    (h : ModularCurve.IsLevelPStructure (W.map φ) p (D.map φ)) : ModularCurve.IsLevelPStructure W p D := by
  have hinj : Function.Injective φ := φ.injective
  have heq : ∀ {x y : K}, (W.map φ).toAffine.Equation (φ x) (φ y) → W.toAffine.Equation x y := by
    intro x y hxy
    rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
    apply hinj
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] at hxy
    simpa only [map_add, map_mul, map_pow] using hxy
  have hpsi : ∀ {x : K}, ((W.map φ).preΨ p).eval (φ x) = 0 → (W.preΨ p).eval x = 0 := by
    intro x hx
    rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hx
    exact hinj (by rw [hx, map_zero])
  have hind : ∀ {x y : K}, IsUnit (ModularCurve.indepElt (W.map φ) p (φ x) (φ y)) → IsUnit (ModularCurve.indepElt W p x y) := by
    intro x y hu
    rw [ModularCurve.indepElt_map] at hu
    rw [isUnit_iff_ne_zero] at hu ⊢
    intro h0; exact hu (by rw [h0, map_zero])
  exact ⟨heq h.equation_P, heq h.equation_Q, hpsi h.preΨ_P, hpsi h.preΨ_Q, hind h.isUnit_indepElt_PQ,
    hind h.isUnit_indepElt_QP⟩

theorem isCyclicKernel_of_map {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {N : ℕ} {h : Polynomial K}
    (hh : (W.map φ).IsCyclicKernel N (h.map φ)) : W.IsCyclicKernel N h := by
  have hinj : Function.Injective φ := φ.injective
  have hdeg : h.natDegree = (h.map φ).natDegree := (Polynomial.natDegree_map_eq_of_injective hinj h).symm
  have hcoeff : h.coeff ((N - 1) / 2) = 1 := by
    apply hinj; rw [← Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  have hmonic : h.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff]
    have hle : h.natDegree ≤ (N - 1) / 2 := hdeg ▸ hh.natDegree_le
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      have := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      rw [hcoeff] at this; exact one_ne_zero this
    · rw [heq]; exact hcoeff
  refine ⟨hdeg ▸ hh.natDegree_le, hcoeff, ?_, ?_⟩
  · have := hh.dvd_preΨ
    rw [WeierstrassCurve.map_preΨ] at this
    exact (Polynomial.map_dvd_map φ hinj hmonic).mp this
  · intro a ha ha'
    have := hh.dvd_smulNumerator a ha ha'
    rw [W.smulNumerator_map φ] at this
    exact (Polynomial.map_dvd_map φ hinj hmonic).mp this

theorem dvd_of_comb_eq_zero {F : Type*} [Field F] {W : WeierstrassCurve F} {ℓ : ℕ} [Fact ℓ.Prime]
    {P Q : W.toAffine.Point}
    (hP : ℓ • P = 0) (hQ : ℓ • Q = 0) (hP0 : P ≠ 0) (hQP : Q ∉ AddSubgroup.zmultiples P)
    (a b : ℤ) (h : a • P + b • Q = 0) : (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hordP : addOrderOf P = ℓ := addOrderOf_eq_prime_iff.mpr ⟨hP, hP0⟩
  have hkill : ∀ (R : W.toAffine.Point) (m : ℤ), ℓ • R = 0 → (ℓ : ℤ) ∣ m → m • R = 0 := by
    intro R m hR ⟨k, hk⟩
    rw [hk, mul_comm, ← smul_smul, natCast_zsmul, hR, smul_zero]
  have hb : (ℓ : ℤ) ∣ b := by
    by_contra hb
    have hb0 : ((b : ℤ) : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    set c : ℤ := (((((b : ℤ) : ZMod ℓ)⁻¹).val : ℕ) : ℤ) with hc
    have hcb : (ℓ : ℤ) ∣ c * b - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hc, Int.cast_natCast, ZMod.natCast_zmod_val, inv_mul_cancel₀ hb0, sub_self]
    apply hQP
    have e1 : Q = c • (b • Q) := by
      have := hkill Q (c * b - 1) hQ hcb
      rw [sub_smul, one_smul, sub_eq_zero] at this
      rw [smul_smul]; exact this.symm
    have e2 : b • Q = -(a • P) := eq_neg_of_add_eq_zero_right h
    rw [e1, e2, smul_neg, smul_smul, ← neg_smul]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-(c * a), rfl⟩
  have hbQ : b • Q = 0 := hkill Q b hQ hb
  have haP : a • P = 0 := by rwa [hbQ, add_zero] at h
  refine ⟨?_, hb⟩
  have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr haP
  rwa [hordP] at this

theorem torsion_basis_of_isLevelPStructure {F : Type*} [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData F) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    (ℓ : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = 0 ∧
    (ℓ : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 ∧
    (∀ a b : ℕ, a < ℓ → b < ℓ →
      (a : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + (b : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 →
      a = 0 ∧ b = 0) := by
  classical
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨hΔ⟩
  have nP := W.toAffine.equation_iff_nonsingular.mp hD.equation_P
  have nQ := W.toAffine.equation_iff_nonsingular.mp hD.equation_Q
  have tors : ∀ {x y : F} (nxy : W.toAffine.Nonsingular x y),
      (W.preΨ ℓ).eval x = 0 → ℓ • WeierstrassCurve.Affine.Point.some _ _ nxy = 0 := by
    intro x y nxy hx
    rw [WeierstrassCurve.preΨ_ofNat] at hx
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nxy).mpr hx
  have tP : ℓ • WeierstrassCurve.Affine.Point.some _ _ nP = 0 := tors nP hD.preΨ_P
  have tQ : ℓ • WeierstrassCurve.Affine.Point.some _ _ nQ = 0 := tors nQ hD.preΨ_Q
  have hP0 : WeierstrassCurve.Affine.Point.some _ _ nP ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hQP : WeierstrassCurve.Affine.Point.some _ _ nQ ∉ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some _ _ nP) :=
    fun hmem => hD.isUnit_indepElt_PQ.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 nP nQ tP).mpr hmem)
  have htoP : ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = WeierstrassCurve.Affine.Point.some _ _ nP := dif_pos nP
  have htoQ : ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = WeierstrassCurve.Affine.Point.some _ _ nQ := dif_pos nQ
  rw [htoP, htoQ]
  refine ⟨by rw [natCast_zsmul]; exact tP, by rw [natCast_zsmul]; exact tQ, ?_⟩
  intro a b ha hb hab
  obtain ⟨h1, h2⟩ := dvd_of_comb_eq_zero tP tQ hP0 hQP a b hab
  exact ⟨Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd_natCast.mp h1) ha,
    Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd_natCast.mp h2) hb⟩

theorem isGamma0PowAt_of_map {K F : Type} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {p k : ℕ} {h : Polynomial K}
    (hh : ModularCurve.IsGamma0PowAt (W.map φ) p k (h.map φ)) : ModularCurve.IsGamma0PowAt W p k h := by
  have hinj : Function.Injective φ := φ.injective
  by_cases hpk : p ^ k = 2
  · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk] at hh ⊢
    refine ⟨(Polynomial.natDegree_map_eq_of_injective hinj h) ▸ hh.natDegree_le, ?_, ?_⟩
    · apply hinj; rw [← Polynomial.coeff_map, hh.coeff_eq_one, map_one]
    · have := hh.dvd_Ψ₂Sq
      rw [WeierstrassCurve.map_Ψ₂Sq] at this
      exact (Polynomial.map_dvd_map' φ).mp this
  · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk] at hh ⊢
    refine ⟨(Polynomial.natDegree_map_eq_of_injective hinj h) ▸ hh.natDegree_le, ?_, ?_, ?_⟩
    · apply hinj; rw [← Polynomial.coeff_map, hh.coeff_eq_one, map_one]
    · have := hh.mul_preΨ_dvd
      rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, ← Polynomial.map_mul] at this
      exact (Polynomial.map_dvd_map' φ).mp this
    · intro a ha ha' hpa
      have := hh.dvd_smulNumerator a ha ha' hpa
      rw [W.smulNumerator_map φ] at this
      exact (Polynomial.map_dvd_map' φ).mp this

end TPAux

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
        IsCoefficientHom W f.toRingHom φ) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L))
      (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K),

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1))) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L (q * ℓ) := by

  classical
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have hN0 : q * ℓ ≠ 0 := Nat.mul_ne_zero hq0 hℓ0
  have hℓ2 : ℓ ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  haveI : NeZero (q * ℓ) := ⟨hN0⟩

  obtain ⟨C, hu, hr, hs, ht, ha1, ha2, ha3, ha4, ha6, hcusp⟩ :=
    ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom q hq M' hqM'
      ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK

  have hφ : ∀ k : ↥K, algebraMap ↥K (LaurentSeries L) k = (k : LaurentSeries L) := fun k => rfl
  have hinj : Function.Injective (algebraMap ↥K (LaurentSeries L)) := (algebraMap ↥K (LaurentSeries L)).injective

  obtain ⟨b1, hb1⟩ := ha1
  obtain ⟨b2, hb2⟩ := ha2
  obtain ⟨b3, hb3⟩ := ha3
  obtain ⟨b4, hb4⟩ := ha4
  obtain ⟨b6, hb6⟩ := ha6
  let W₀ : WeierstrassCurve ↥K := ⟨b1, b2, b3, b4, b6⟩
  have hW₀ : W₀.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L (q * ℓ) := by
    exact WeierstrassCurve.ext hb1 hb2 hb3 hb4 hb6
  have hΔ₀ : IsUnit W₀.Δ := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu' : IsUnit (C • ModularCurve.tateBase L (q * ℓ)).Δ :=
      (ModularCurve.tateBase L (q * ℓ)).isUnit_Δ_variableChange C (ModularCurve.isUnit_Δ_tateBase L (q * ℓ))
    rw [← hW₀, WeierstrassCurve.map_Δ, h0, map_zero] at hu'
    exact not_isUnit_zero hu'

  have hξu : ((hξ.isUnit hN0).unit : L) = ξ := IsUnit.unit_spec _
  have hℓL : IsUnit ((ℓ : ℕ) : L) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hℓ0)
  have hqL : IsUnit ((q : ℕ) : L) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hq0)
  have hsumℓ : ∑ i ∈ Finset.range ℓ, ((((hξ.isUnit hN0).unit : Lˣ) : L) ^ (q * ℓ / ℓ)) ^ i = 0 := by
    rw [hξu, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hℓ0)]
    exact (hξ.pow (Nat.pos_of_ne_zero hN0) rfl).geom_sum_eq_zero (by omega)
  have hsumq : ∑ i ∈ Finset.range q, ((((hξ.isUnit hN0).unit : Lˣ) : L) ^ (q * ℓ / q)) ^ i = 0 := by
    rw [hξu, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq0)]
    exact (hξ.pow (Nat.pos_of_ne_zero hN0) (Nat.mul_comm q ℓ)).geom_sum_eq_zero (by omega)

  have hidx : ∀ m : ℕ, m ≠ 0 → m < q * ℓ → ((m : ZMod (q * ℓ)) ≠ 0) := by
    intro m hm hlt h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h) (not_le.mpr hlt)
  have hqlt : q < q * ℓ := lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hq0) (by omega)
  have hℓlt : ℓ < q * ℓ := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hℓ0) (by omega)
  have hv1 : (![(q : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h =>
    hidx q hq0 hqlt (by simpa using congrFun h 0)
  have hv2 : (![0, -(q : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h =>
    hidx q hq0 hqlt (by simpa using congrFun h 1)
  have hv3 : (![(ℓ : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h =>
    hidx ℓ hℓ0 hℓlt (by simpa using congrFun h 0)
  have hv4 : (![0, -(ℓ : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h =>
    hidx ℓ hℓ0 hℓlt (by simpa using congrFun h 1)

  obtain ⟨xP, hxP⟩ := (hcusp _ _ hv1 hv2).1
  obtain ⟨yP, hyP⟩ := (hcusp _ _ hv1 hv2).2
  obtain ⟨xQ, hxQ⟩ := (hcusp _ _ hv2 hv1).1
  obtain ⟨yQ, hyQ⟩ := (hcusp _ _ hv2 hv1).2
  let D₀ : ModularCurve.LevelPData ↥K := ⟨xP, yP, xQ, yQ⟩
  have hD₀map : D₀.map (algebraMap ↥K (LaurentSeries L)) =
      (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit hN0).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]).variableChange C := by
    refine ModularCurve.LevelPData.ext hxP hyP ?_ ?_
    · exact hxQ
    · exact hyQ
  have hTwℓ : ModularCurve.IsLevelPStructure (ModularCurve.tateBase L (q * ℓ)) ℓ
      (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit hN0).unit ![(q : ZMod (q * ℓ)), 0] ![0, -(q : ZMod (q * ℓ))]) := by
    have := ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd (R := L) (p := ℓ) hℓ2 hℓL (q * ℓ)
      (dvd_mul_left ℓ q) (hξ.isUnit hN0).unit hsumℓ
    rwa [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hℓ0)] at this
  have hD₀ : ModularCurve.IsLevelPStructure W₀ ℓ D₀ :=
    TPAux.isLevelPStructure_of_map (algebraMap ↥K (LaurentSeries L)) (by rw [hW₀, hD₀map]; exact hTwℓ.variableChange C)

  obtain ⟨Px, hPx⟩ := (hcusp _ _ hv3 hv4).1
  obtain ⟨Py, hPy⟩ := (hcusp _ _ hv3 hv4).2
  obtain ⟨Qx, hQx⟩ := (hcusp _ _ hv4 hv3).1
  obtain ⟨Qy, hQy⟩ := (hcusp _ _ hv4 hv3).2
  let Dq : ModularCurve.LevelPData ↥K := ⟨Px, Py, Qx, Qy⟩
  have hDqmap : Dq.map (algebraMap ↥K (LaurentSeries L)) =
      (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit hN0).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]).variableChange C := by
    refine ModularCurve.LevelPData.ext hPx hPy ?_ ?_
    · exact hQx
    · exact hQy
  have hTwq : ModularCurve.IsLevelPStructure (ModularCurve.tateBase L (q * ℓ)) q
      (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit hN0).unit ![(ℓ : ZMod (q * ℓ)), 0] ![0, -(ℓ : ZMod (q * ℓ))]) := by
    have := ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd (R := L) (p := q) hq2 hqL (q * ℓ)
      (dvd_mul_right q ℓ) (hξ.isUnit hN0).unit hsumq
    rwa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq0)] at this
  have hDq : ModularCurve.IsLevelPStructure W₀ q Dq :=
    TPAux.isLevelPStructure_of_map (algebraMap ↥K (LaurentSeries L)) (by rw [hW₀, hDqmap]; exact hTwq.variableChange C)

  obtain ⟨SP, hSP⟩ := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    (W₀ : WeierstrassCurve.Projective ↥K)).1 Px Py).mp hDq.equation_P
  obtain ⟨SQ, hSQ⟩ := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    (W₀ : WeierstrassCurve.Projective ↥K)).1 Qx Qy).mp hDq.equation_Q
  have hqK : ((q : ℕ) : ↥K) ≠ 0 := by
    intro h0
    apply hqL.ne_zero
    have := congrArg (algebraMap ↥K (LaurentSeries L)) h0
    rw [map_natCast, map_zero] at this
    have h2 : (algebraMap L (LaurentSeries L)) (q : L) = 0 := by rw [map_natCast]; exact this
    exact (algebraMap L (LaurentSeries L)).injective (by rw [h2, map_zero])
  obtain ⟨tP, tQ, hind⟩ := TPAux.torsion_basis_of_isLevelPStructure q hq2 W₀ hΔ₀ Dq hDq
  have hDrin : IsDrinfeldBasis (𝒢 ↥K W₀ hΔ₀) q SP SQ :=
    WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isSectionThrough_of_torsion_basis A 𝒢 h𝒢 h𝒢O
      (W₀ : WeierstrassCurve.Projective ↥K) hΔ₀ q hqK SP SQ Px Py Qx Qy hSP hSQ tP tQ hind

  letI algA : Algebra A (LaurentSeries L) := ((algebraMap L (LaurentSeries L)).comp (algebraMap A L)).toAlgebra
  have h2lt : 2 < q * ℓ := by omega
  have h10 : (![(1 : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h =>
    hidx 1 one_ne_zero (by omega) (by simpa using congrFun h 0)
  have h20 : (![(2 : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h =>
    hidx 2 (by omega) h2lt (by simpa using congrFun h 0)
  have hcomp : ∀ p : ↥M'.primeFactors, ∃ h₀ : Polynomial ↥K,
      ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) h₀ ∧
      ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        (h₀.map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ) (ζ ^ a)).1)) := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    haveI : Fact (p : ℕ).Prime := ⟨hp⟩
    have hpL : ((p : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' (p : ℕ)
    obtain ⟨h, hhk, hh⟩ :=
      ModularCurve.exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint L (p : ℕ)
        (M'.factorization (p : ℕ)) hpL (q * ℓ)
    have hhC := hM (LaurentSeries L) (ModularCurve.tateBase L (q * ℓ)) C (p : ℕ) (M'.factorization (p : ℕ)) h hhk
    have hcoefK :=
      ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow
        q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK (p : ℕ) (M'.factorization (p : ℕ)) hpk h
        (fun F' _ f ζ' hζ' => hh F' f ζ' hζ') C (hcusp _ _ h10 h20).1 (hcusp _ _ h20 h10).1
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : Polynomial ↥K, h₀.map (algebraMap ↥K (LaurentSeries L)) =
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) h := by
      have hl : ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) h ∈
          Polynomial.lifts (algebraMap ↥K (LaurentSeries L)) :=
        (Polynomial.lifts_iff_coeff_lifts _).mpr (fun n => hcoefK n)
      obtain ⟨h₀, hh₀⟩ := RingHom.mem_rangeS.mp hl
      exact ⟨h₀, hh₀⟩
    refine ⟨h₀, TPAux.isGamma0PowAt_of_map (algebraMap ↥K (LaurentSeries L)) (by rw [hW₀, hh₀]; exact hhC), ?_⟩
    intro F' _ f ζ' hζ'
    rw [hh₀, ModularCurve.kernelVariableChangeDeg_map, hh F' f ζ' hζ']
  choose hT hTspec hTtoric using hcomp

  refine ⟨C, ⟨W₀, hΔ₀, (hT, (D₀, ⟨W₀, SP, SQ⟩)), ⟨hTspec, hD₀, rfl, hΔ₀, hDrin⟩⟩, ⟨hu, hr, hs, ht⟩, hW₀,
    (fun p F' _ f ζ' hζ' => hTtoric p F' f ζ' hζ'), hD₀map,
    ⟨Px, Py, Qx, Qy, hPx, hPy, hQx, hQy, hSP, hSQ⟩, ?_⟩

  have key : ∀ (W' : WeierstrassCurve (LaurentSeries L)) (h' : IsUnit W'.Δ),
      W' = C • ModularCurve.tateBase L (q * ℓ) → W'.jOfUnit h' = ModularCurve.jqNModC L (q * ℓ) := by
    intro W' h' e
    subst e
    rw [(ModularCurve.tateBase L (q * ℓ)).jOfUnit_variableChange C (ModularCurve.isUnit_Δ_tateBase L (q * ℓ)) h']
    show ((ModularCurve.tateLaurent L).map (ModularCurve.qExpand L (q * ℓ))).jOfUnit (ModularCurve.isUnit_Δ_tateBase L (q * ℓ)) =
      ModularCurve.qExpand L (q * ℓ) (ModularCurve.jqModC L)
    rw [(ModularCurve.tateLaurent L).jOfUnit_map (ModularCurve.qExpand L (q * ℓ)) (ModularCurve.tateLaurent L).isUnit_Δ
      (ModularCurve.isUnit_Δ_tateBase L (q * ℓ)), WeierstrassCurve.jOfUnit_eq_j, ModularCurve.j_tateLaurent]
  have key2 : ∀ (V : WeierstrassCurve ↥K) (hV : IsUnit V.Δ), V = W₀ →
      ((V.jOfUnit hV : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) := by
    intro V hV e
    subst e
    show algebraMap ↥K (LaurentSeries L) (W₀.jOfUnit hV) = _
    rw [← W₀.jOfUnit_map (algebraMap ↥K (LaurentSeries L)) hV (W₀.isUnit_Δ_map _ hV)]
    exact key _ _ hW₀
  dsimp only [ModularCurve.RigidWeierstrassData.toLevelModuliDatum]
  rw [ModularCurve.RigidWeierstrassData.jOf_mk]
  exact key2 _ _ rfl

end S_ModularCurve_FullLevel_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_gamma0Pow (solution)
