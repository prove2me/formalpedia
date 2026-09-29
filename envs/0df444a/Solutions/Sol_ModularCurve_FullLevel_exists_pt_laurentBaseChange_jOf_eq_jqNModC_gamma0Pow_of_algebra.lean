-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/4d4e94cd-1d74-5007-827d-e1f8bac2cabe

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
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
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_of_dvd
import Theorems.Thm_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod
import Theorems.Thm_ModularCurve_exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
import Theorems.Thm_ModularCurve_FullLevel_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
import Theorems.Thm_ModularCurve_j_map_qExpand_tateLaurent
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

noncomputable section

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
p2m_open "Polynomial AlgebraicGeometry.Polynomial NeronModelInfra"

open scoped MatrixGroups

namespace P2MTatePowAsm

section Descent

variable {K T : Type*} [Field K] [Field T] (g : K →+* T)

theorem isLevelPStructure_of_map (W : WeierstrassCurve K) (p : ℕ) (D : LevelPData K)
    (h : IsLevelPStructure (W.map g) p (D.map g)) : IsLevelPStructure W p D where
  equation_P := (WeierstrassCurve.Affine.map_equation W.toAffine g.injective D.xP D.yP).mp h.equation_P
  equation_Q := (WeierstrassCurve.Affine.map_equation W.toAffine g.injective D.xQ D.yQ).mp h.equation_Q
  preΨ_P := by
    have h1 := h.preΨ_P
    rw [LevelPData.map_xP, WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h1
    exact g.injective (by rw [h1, map_zero])
  preΨ_Q := by
    have h1 := h.preΨ_Q
    rw [LevelPData.map_xQ, WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h1
    exact g.injective (by rw [h1, map_zero])
  isUnit_indepElt_PQ := by
    have h1 := h.isUnit_indepElt_PQ
    rw [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map] at h1
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  isUnit_indepElt_QP := by
    have h1 := h.isUnit_indepElt_QP
    rw [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map] at h1
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1

theorem isTwoKernel_of_map (W : WeierstrassCurve K) (h : K[X])
    (hh : (W.map g).IsTwoKernel (h.map g)) : W.IsTwoKernel h where
  natDegree_le := by
    have := hh.natDegree_le
    rwa [Polynomial.natDegree_map] at this
  coeff_eq_one := by
    have := hh.coeff_eq_one
    rw [Polynomial.coeff_map] at this
    exact g.injective (by rw [this, map_one])
  dvd_Ψ₂Sq := by
    have := hh.dvd_Ψ₂Sq
    rw [WeierstrassCurve.map_Ψ₂Sq] at this
    exact (Polynomial.map_dvd_map' g).mp this

theorem isCyclicGenKernel_of_map (W : WeierstrassCurve K) (p k : ℕ) (h : K[X])
    (hh : (W.map g).IsCyclicGenKernel p k (h.map g)) : W.IsCyclicGenKernel p k h where
  natDegree_le := by
    have := hh.natDegree_le
    rwa [Polynomial.natDegree_map] at this
  coeff_eq_one := by
    have := hh.coeff_eq_one
    rw [Polynomial.coeff_map] at this
    exact g.injective (by rw [this, map_one])
  mul_preΨ_dvd := by
    have := hh.mul_preΨ_dvd
    rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, ← Polynomial.map_mul] at this
    exact (Polynomial.map_dvd_map' g).mp this
  dvd_smulNumerator := fun a ha ha' hpa => by
    have := hh.dvd_smulNumerator a ha ha' hpa
    rw [WeierstrassCurve.smulNumerator_map] at this
    exact (Polynomial.map_dvd_map' g).mp this

theorem isGamma0PowAt_of_map (W : WeierstrassCurve K) (p k : ℕ) (h : K[X])
    (hh : ModularCurve.IsGamma0PowAt (W.map g) p k (h.map g)) : ModularCurve.IsGamma0PowAt W p k h := by
  by_cases hpk : p ^ k = 2
  · exact (ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk _).2
      (isTwoKernel_of_map g W h ((ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk _).1 hh))
  · exact (ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk _).2
      (isCyclicGenKernel_of_map g W p k h ((ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk _).1 hh))

end Descent

section CastOver

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
variable {T : Scheme.{u}}

def castOver {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨x.1, x.2.trans e⟩

theorem castOver_injective {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t') :
    Function.Injective (castOver (f := f) e) := by
  intro x y h
  have h1 : (castOver e x).1 = (castOver e y).1 := congrArg Subtype.val h
  exact Subtype.ext h1

theorem castOver_mul (G : RelativeGroupLaw R f) {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t')
    (x y : SchemeHomOver t f) : G.mul t' (castOver e x) (castOver e y) = castOver e (G.mul t x y) := by
  subst e; rfl

theorem castOver_one (G : RelativeGroupLaw R f) {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t') :
    G.one t' = castOver e (G.one t) := by
  subst e; rfl

theorem castOver_nsmul (G : RelativeGroupLaw R f) {t t' : T ⟶ Spec (CommRingCat.of R)} (e : t = t')
    (n : ℕ) (x : SchemeHomOver t f) : G.nsmul t' n (castOver e x) = castOver e (G.nsmul t n x) := by
  subst e; rfl

end CastOver

section Ev

universe u

variable {K : Type u} [Field K] (W : WeierstrassCurve.Projective K)
  (G : RelativeGroupLaw K (projModelStrCR W))
  (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra K F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W) ≃
      (W.baseChange F).toAffine.Point)
  (hev : IsPointsEval W G ev)

variable (F : Type u) [Field F] [DecidableEq F] [Algebra K F]

include hev in
theorem ev_one : ev F (G.one _) = 0 := by
  have h := hev.1 F (G.one _) (G.one _)
  rw [G.one_mul] at h

  have : ev F (G.one _) + ev F (G.one _) = ev F (G.one _) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

include hev in
theorem ev_nsmul (n : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) (projModelStrCR W)) :
    ev F (G.nsmul _ n x) = n • ev F x := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, zero_smul]; exact ev_one W G ev hev F
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, hev.1, ih, succ_nsmul]

end Ev

section Arith

theorem zmod_natCast_ne_zero {N a : ℕ} [NeZero N] (ha0 : 0 < a) (ha : a < N) : ((a : ℕ) : ZMod N) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd ha0 h) (not_le.mpr ha)

theorem vec_ne_zero_of_fst {N : ℕ} {a b : ZMod N} (ha : a ≠ 0) : (![a, b] : Fin 2 → ZMod N) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this
  exact ha this

theorem vec_ne_zero_of_snd {N : ℕ} {a b : ZMod N} (hb : b ≠ 0) : (![a, b] : Fin 2 → ZMod N) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this
  exact hb this

end Arith

end P2MTatePowAsm

end

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (A₀ : Type) [CommRing A₀] [Algebra A₀ ↥K]
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
        IsCoefficientHom W f.toRingHom φ) :
    ∃ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K,
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L (q * ℓ) := by
  classical

  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  have hN0 : q * ℓ ≠ 0 := Nat.mul_ne_zero hqp.ne_zero hℓp.ne_zero
  haveI hNz : NeZero (q * ℓ) := ⟨hN0⟩
  have hNpos : 0 < q * ℓ := Nat.pos_of_ne_zero hN0
  have hq2 : q ≠ 2 := by omega
  have hℓ2 : ℓ ≠ 2 := by omega
  set ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
    with hξu
  have hξu_val : (ξu : L) = ξ := rfl

  set g : ↥K →+* LaurentSeries L := algebraMap ↥K (LaurentSeries L) with hg
  have hg_apply : ∀ x : ↥K, g x = (x : LaurentSeries L) := fun x => IntermediateField.algebraMap_apply K x
  have hrange : ∀ {y : LaurentSeries L}, y ∈ Set.range ((↑) : ↥K → LaurentSeries L) → ∃ x : ↥K, g x = y := by
    intro y hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by rw [hg_apply, hx]⟩

  obtain ⟨C, ha₁, ha₂, ha₃, ha₄, ha₆, hcusp⟩ :=
    ModularCurve.FullLevel.exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem q hq M' hqM' ℓ
      hℓ3 hℓq hℓM' L ζ hζ ξ hξ K hK
  obtain ⟨k₁, hk₁⟩ := hrange ha₁
  obtain ⟨k₂, hk₂⟩ := hrange ha₂
  obtain ⟨k₃, hk₃⟩ := hrange ha₃
  obtain ⟨k₄, hk₄⟩ := hrange ha₄
  obtain ⟨k₆, hk₆⟩ := hrange ha₆
  set W : WeierstrassCurve ↥K := ⟨k₁, k₂, k₃, k₄, k₆⟩ with hWdef
  have hW : W.map g = C • tateBase L (q * ℓ) := by
    ext
    · rw [WeierstrassCurve.map_a₁, hk₁]
    · rw [WeierstrassCurve.map_a₂, hk₂]
    · rw [WeierstrassCurve.map_a₃, hk₃]
    · rw [WeierstrassCurve.map_a₄, hk₄]
    · rw [WeierstrassCurve.map_a₆, hk₆]
  have hΔ' : IsUnit (C • tateBase L (q * ℓ)).Δ :=
    (tateBase L (q * ℓ)).isUnit_Δ_variableChange C (isUnit_Δ_tateBase L (q * ℓ))
  have hΔ : IsUnit W.Δ := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 : (W.map g).Δ = 0 := by rw [WeierstrassCurve.map_Δ, h0, map_zero]
    rw [hW] at h1
    exact hΔ'.ne_zero h1

  have level : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ q * ℓ → IsPrimitiveRoot (ξ ^ (q * ℓ / p)) p →
      ∃ D : LevelPData ↥K, IsLevelPStructure W p D := by
    intro p _ hp2 hpd hprim
    have hpp : p.Prime := Fact.out
    have hpunit : IsUnit ((p : ℕ) : L) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hpp.ne_zero)
    have hsum : ∑ i ∈ Finset.range p, ((ξu : L) ^ (q * ℓ / p)) ^ i = 0 :=
      hprim.geom_sum_eq_zero hpp.one_lt
    have hT := ModularCurve.isLevelPStructure_tateBase_cuspData_of_dvd (R := L) hp2 hpunit (q * ℓ) hpd ξu hsum

    have hT' := hT.variableChange C

    have hidx0 : 0 < q * ℓ / p := Nat.div_pos (Nat.le_of_dvd hNpos hpd) hpp.pos
    have hidx : q * ℓ / p < q * ℓ := Nat.div_lt_self hNpos hpp.one_lt
    have hv : (![((q * ℓ / p : ℕ) : ZMod (q * ℓ)), 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 :=
      P2MTatePowAsm.vec_ne_zero_of_fst (P2MTatePowAsm.zmod_natCast_ne_zero hidx0 hidx)
    have hw : (![0, ((q * ℓ / p : ℕ) : ZMod (q * ℓ))] : Fin 2 → ZMod (q * ℓ)) ≠ 0 :=
      P2MTatePowAsm.vec_ne_zero_of_snd (P2MTatePowAsm.zmod_natCast_ne_zero hidx0 hidx)
    obtain ⟨hxP, hyP⟩ := hcusp _ _ hv hw
    obtain ⟨hxQ, hyQ⟩ := hcusp _ _ hw hv
    rw [← cuspData_swap, LevelPData.variableChange_swap, LevelPData.swap_xP] at hxQ
    rw [← cuspData_swap, LevelPData.variableChange_swap, LevelPData.swap_yP] at hyQ
    obtain ⟨xP, hxP'⟩ := hrange hxP
    obtain ⟨yP, hyP'⟩ := hrange hyP
    obtain ⟨xQ, hxQ'⟩ := hrange hxQ
    obtain ⟨yQ, hyQ'⟩ := hrange hyQ
    refine ⟨⟨xP, yP, xQ, yQ⟩, P2MTatePowAsm.isLevelPStructure_of_map g W p _ ?_⟩
    rw [hW]
    convert hT' using 1 <;> first | rfl | (ext <;> simp [LevelPData.map, hxP', hyP', hxQ', hyQ', hξu]; done)
  obtain ⟨Dℓ, hDℓ⟩ := level ℓ hℓ2 (dvd_mul_left ℓ q) (by
    rw [Nat.mul_div_cancel q hℓp.pos]
    exact hξ.pow hNpos rfl)
  obtain ⟨Dq, hDq⟩ := level q hq2 (dvd_mul_right q ℓ) (by
    rw [Nat.mul_div_cancel_left ℓ hqp.pos]
    exact hξ.pow hNpos (Nat.mul_comm q ℓ))

  letI instAlg : Algebra A₀ (LaurentSeries L) := ((algebraMap ↥K (LaurentSeries L)).comp (algebraMap A₀ ↥K)).toAlgebra
  have h1lt : 1 < q * ℓ := by nlinarith
  have h2lt : 2 < q * ℓ := by nlinarith
  have h10 : (![1, 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := by
    have := P2MTatePowAsm.zmod_natCast_ne_zero (N := q * ℓ) (a := 1) one_pos h1lt
    rw [Nat.cast_one] at this
    exact P2MTatePowAsm.vec_ne_zero_of_fst this
  have h20 : (![2, 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := by
    have := P2MTatePowAsm.zmod_natCast_ne_zero (N := q * ℓ) (a := 2) two_pos h2lt
    rw [Nat.cast_ofNat] at this
    exact P2MTatePowAsm.vec_ne_zero_of_fst this
  obtain ⟨hx1, -⟩ := hcusp _ _ h10 h20
  obtain ⟨hx2, -⟩ := hcusp _ _ h20 h10

  have hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by
    let pb : PowerBasis ℚ L := hξ.powerBasis ℚ
    have hgen : pb.gen = ξ := IsPrimitiveRoot.powerBasis_gen ℚ hξ
    have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) (q * ℓ) := by
      have := Complex.isPrimitiveRoot_exp (q * ℓ) hN0
      push_cast at this
      exact this
    have hy : Polynomial.aeval (Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) (minpoly ℚ pb.gen) = 0 := by
      rw [hgen, ← Polynomial.cyclotomic_eq_minpoly_rat hξ hNpos, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_cyclotomic]
      exact Polynomial.isRoot_cyclotomic_iff.mpr hz
    refine ⟨(pb.lift _ hy).toRingHom, ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← hgen]
    exact pb.lift_gen _ hy
  have hΓ : ∀ pp : ↥M'.primeFactors, ∃ h₀ : Polynomial ↥K,
      ModularCurve.IsGamma0PowAt W (pp : ℕ) (M'.factorization (pp : ℕ)) h₀ := by
    intro pp
    have hpprime : (pp : ℕ).Prime := Nat.prime_of_mem_primeFactors pp.2
    haveI : Fact (pp : ℕ).Prime := ⟨hpprime⟩
    have hpL : (((pp : ℕ) : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr hpprime.ne_zero
    obtain ⟨h, hhK, hhmap⟩ :=
      ModularCurve.exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
        L (pp : ℕ) (M'.factorization (pp : ℕ)) hpL (q * ℓ)
    have hh₁ : ModularCurve.IsGamma0PowAt (C • tateBase L (q * ℓ)) (pp : ℕ) (M'.factorization (pp : ℕ))
        (kernelVariableChangeDeg C (gamma0PowDeg (pp : ℕ) (M'.factorization (pp : ℕ))) h) :=
      hM (LaurentSeries L) (tateBase L (q * ℓ)) C (pp : ℕ) (M'.factorization (pp : ℕ)) h hhK
    have hpk : (pp : ℕ) ^ M'.factorization (pp : ℕ) ∣ M' := Nat.ordProj_dvd M' _
    have hcoef :=
      ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow
        q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK (pp : ℕ) (M'.factorization (pp : ℕ)) hpk h
        (fun F' _ f ζ' hζ' => hhmap F' f ζ' hζ') C hx1 hx2
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : Polynomial ↥K,
        h₀.map g = kernelVariableChangeDeg C (gamma0PowDeg (pp : ℕ) (M'.factorization (pp : ℕ))) h := by
      rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      intro i
      obtain ⟨x, hx⟩ := hrange (hcoef i)
      exact ⟨x, hx⟩
    exact ⟨h₀, P2MTatePowAsm.isGamma0PowAt_of_map g W _ _ h₀ (by rw [hW, hh₀]; exact hh₁)⟩
  choose hΓfun hΓspec using hΓ

  haveI : CharZero ↥K := charZero_of_injective_algebraMap (algebraMap L ↥K).injective
  have hqK : ((q : ℕ) : ↥K) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne_zero
  set G : RelativeGroupLaw ↥K (projModelStrCR (W : WeierstrassCurve.Projective ↥K)) := 𝒢 ↥K W hΔ with hGdef
  obtain ⟨ev, hev⟩ := h𝒢 ↥K W hΔ
  haveI : (W.baseChange ↥K).IsElliptic :=
    ⟨by rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]; exact hΔ.map _⟩
  have hDq' : IsLevelPStructure (W.baseChange ↥K) q (Dq.map (algebraMap ↥K ↥K)) := hDq.map _
  obtain ⟨fb, hfb⟩ :=
    ModularCurve.IsLevelPStructure.exists_injective_addMonoidHom_zmod_prod (W.baseChange ↥K) hq2 hqK hDq'
  set P₀ : (W.baseChange ↥K).toAffine.Point := fb (1, 0) with hP₀
  set Q₀ : (W.baseChange ↥K).toAffine.Point := fb (0, 1) with hQ₀
  have hcomb : ∀ a b : ℕ, a • P₀ + b • Q₀ = fb ((a : ZMod q), (b : ZMod q)) := by
    intro a b
    rw [hP₀, hQ₀, ← map_nsmul, ← map_nsmul, ← map_add]
    congr 1
    ext <;> simp

  have ht : Spec.map (CommRingCat.ofHom (algebraMap ↥K ↥K)) = 𝟙 (Spec (CommRingCat.of ↥K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
  set P : Section (W : WeierstrassCurve.Projective ↥K) := P2MTatePowAsm.castOver ht ((ev ↥K).symm P₀) with hPdef
  set Q : Section (W : WeierstrassCurve.Projective ↥K) := P2MTatePowAsm.castOver ht ((ev ↥K).symm Q₀) with hQdef
  have hnsP : ∀ (n : ℕ) (R₀ : (W.baseChange ↥K).toAffine.Point),
      G.nsmul (𝟙 _) n (P2MTatePowAsm.castOver ht ((ev ↥K).symm R₀)) =
        P2MTatePowAsm.castOver ht ((ev ↥K).symm (n • R₀)) := by
    intro n R₀
    rw [P2MTatePowAsm.castOver_nsmul]
    congr 1
    apply (ev ↥K).injective
    rw [P2MTatePowAsm.ev_nsmul W G ev hev, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hone : G.one (𝟙 _) = P2MTatePowAsm.castOver ht ((ev ↥K).symm 0) := by
    rw [P2MTatePowAsm.castOver_one G ht]
    congr 1
    apply (ev ↥K).injective
    rw [P2MTatePowAsm.ev_one W G ev hev, Equiv.apply_symm_apply]
  have hlin : ∀ a b : ℕ, linComb G P Q a b =
      P2MTatePowAsm.castOver ht ((ev ↥K).symm (fb ((a : ZMod q), (b : ZMod q)))) := by
    intro a b
    rw [linComb, hPdef, hQdef, hnsP, hnsP, P2MTatePowAsm.castOver_mul]
    congr 1
    apply (ev ↥K).injective
    rw [hev.1, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hcomb]
  have htors : ∀ R₀ : ZMod q × ZMod q, q • fb R₀ = 0 := by
    intro R₀
    rw [← map_nsmul, ← map_zero fb]
    congr 1
    ext <;> simp
  have hP : G.nsmul (𝟙 _) q P = G.one (𝟙 _) := by
    rw [hPdef, hnsP, hone, hP₀, htors]
  have hQ : G.nsmul (𝟙 _) q Q = G.one (𝟙 _) := by
    rw [hQdef, hnsP, hone, hQ₀, htors]
  have hinj : ∀ a b a' b' : ℕ, a < q → b < q → a' < q → b' < q →
      linComb G P Q a b = linComb G P Q a' b' → a = a' ∧ b = b' := by
    intro a b a' b' ha hb ha' hb' heq
    rw [hlin, hlin] at heq
    have h1 := (ev ↥K).symm.injective (P2MTatePowAsm.castOver_injective ht heq)
    have h2 := hfb h1
    simp only [Prod.mk.injEq] at h2
    constructor
    · have := (ZMod.natCast_eq_natCast_iff' a a' q).mp h2.1
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
    · have := (ZMod.natCast_eq_natCast_iff' b b' q).mp h2.2
      rwa [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at this
  have hDB : IsDrinfeldBasis G q P Q :=
    WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isPointsEval_of_nsmul_eq_one_of_linComb_inj
      (W : WeierstrassCurve.Projective ↥K) hΔ G ev hev q hqK P Q hP hQ hinj

  let xD : RawDrinfeldPair ↥K := ⟨W, P, Q⟩
  have hxD : RawDrinfeldPair.IsLevel 𝒢 q (W : WeierstrassCurve.Projective ↥K) xD := ⟨rfl, hΔ, hDB⟩
  let raw : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw ↥K :=
    ⟨W, hΔ, (hΓfun, (Dℓ, xD)), ⟨hΓspec, hDℓ, hxD⟩⟩
  refine ⟨Quot.mk _ raw, ?_⟩
  change ((W.jOfUnit hΔ : ↥K) : LaurentSeries L) = jqNModC L (q * ℓ)
  have hΔmap : IsUnit (W.map g).Δ := W.isUnit_Δ_map g hΔ
  rw [← hg_apply, ← WeierstrassCurve.jOfUnit_map W g hΔ hΔmap]
  have key : ∀ (W' : WeierstrassCurve (LaurentSeries L)) (hW' : IsUnit W'.Δ),
      W' = C • tateBase L (q * ℓ) → W'.jOfUnit hW' = jqNModC L (q * ℓ) := by
    intro W' hW' e
    subst e
    rw [WeierstrassCurve.jOfUnit_variableChange _ C (isUnit_Δ_tateBase L (q * ℓ)),
      WeierstrassCurve.jOfUnit_eq_j]
    exact ModularCurve.j_map_qExpand_tateLaurent L (q * ℓ)
  exact key _ hΔmap hW

end S_ModularCurve_FullLevel_exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_pt_laurentBaseChange_jOf_eq_jqNModC_gamma0Pow_of_algebra (solution)
