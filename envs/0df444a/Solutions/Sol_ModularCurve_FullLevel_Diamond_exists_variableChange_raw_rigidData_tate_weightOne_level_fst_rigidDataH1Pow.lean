-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1f22d0fa-1e27-5bb7-b2ba-de38027038d7

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom_pinGamma1
import Theorems.Thm_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow
import Theorems.Thm_ModularCurve_isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_dvd_inLineMulPoly_of_map_eq_variableChange_tateBase_tateToricPoint_of_map_eq_kernelVariableChangeDeg
import Theorems.Thm_ModularCurve_torsion_basis_of_map_eq_variableChange_tateBase_cuspData
import Theorems.Thm_ModularCurve_exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
import Theorems.Thm_ModularCurve_j_tateLaurent
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace TPH1Aux

theorem isGamma1Point_of_map {K F : Type} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {ℓ : ℕ} {D : ModularCurve.LevelPData K}
    (h : ModularCurve.IsGamma1Point (W.map φ) ℓ (D.map φ)) : ModularCurve.IsGamma1Point W ℓ D := by
  have hinj : Function.Injective φ := φ.injective
  have heq : ∀ {x y : K}, (W.map φ).toAffine.Equation (φ x) (φ y) → W.toAffine.Equation x y := by
    intro x y hxy
    rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
    apply hinj
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] at hxy
    simpa only [map_add, map_mul, map_pow] using hxy
  have hpsi : ∀ {x : K}, ((W.map φ).preΨ ℓ).eval (φ x) = 0 → (W.preΨ ℓ).eval x = 0 := by
    intro x hx
    rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hx
    exact hinj (by rw [hx, map_zero])
  refine ⟨heq h.equation_P, hpsi h.preΨ_P, hinj ?_, hinj ?_⟩
  · have := h.xQ_eq; rwa [ModularCurve.LevelPData.map_xQ, ModularCurve.LevelPData.map_xP] at this
  · have := h.yQ_eq; rwa [ModularCurve.LevelPData.map_yQ, ModularCurve.LevelPData.map_yP] at this

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

end TPH1Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
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
        IsCoefficientHom W f.toRingHom φ) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L))
      (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K),

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L q ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) =
        (⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xP ∧
        (Py : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yP ∧
        (Qx : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xQ ∧
        (Qy : LaurentSeries L) = ((ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yQ ∧
        IsSectionThrough x.level.2.2.P Px Py ∧ IsSectionThrough x.level.2.2.Q Qx Qy) ∧

      (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf (Quot.mk _ x) : ↥K) : LaurentSeries L) =
        ModularCurve.jqNModC L q := by
  classical
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hℓg0 : ℓg ≠ 0 := hℓg.ne_zero
  have hN0 : q * ℓg ≠ 0 := Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero
  have hℓg2 : ℓg ≠ 2 := by omega
  have hℓg11 : 11 ≤ ℓg := by omega
  haveI : NeZero q := ⟨hq0⟩

  obtain ⟨C, hu, hr, hs, ht, ha1, ha2, ha3, ha4, ha6, hcusp, htoric⟩ :=
    ModularCurve.FullLevel.Diamond.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom_pinGamma1
      q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ hιξ H₁ hH₁ K hK
  have hinj : Function.Injective (algebraMap ↥K (LaurentSeries L)) := (algebraMap ↥K (LaurentSeries L)).injective

  obtain ⟨b1, hb1⟩ := ha1
  obtain ⟨b2, hb2⟩ := ha2
  obtain ⟨b3, hb3⟩ := ha3
  obtain ⟨b4, hb4⟩ := ha4
  obtain ⟨b6, hb6⟩ := ha6
  let W₀ : WeierstrassCurve ↥K := ⟨b1, b2, b3, b4, b6⟩
  have hW₀ : W₀.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L q := by
    exact WeierstrassCurve.ext hb1 hb2 hb3 hb4 hb6
  have hΔ₀ : IsUnit W₀.Δ := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu' : IsUnit (C • ModularCurve.tateBase L q).Δ :=
      (ModularCurve.tateBase L q).isUnit_Δ_variableChange C (ModularCurve.isUnit_Δ_tateBase L q)
    rw [← hW₀, WeierstrassCurve.map_Δ, h0, map_zero] at hu'
    exact not_isUnit_zero hu'

  have hξu : (((hξ.isUnit hN0).unit : Lˣ) : L) = ξ := IsUnit.unit_spec _
  have hcq : IsPrimitiveRoot ((((hξ.isUnit hN0).unit ^ q : Lˣ)) : L) ℓg := by
    rw [Units.val_pow_eq_pow_val, hξu]; exact hξ.pow (Nat.pos_of_ne_zero hN0) rfl
  have hζq : IsPrimitiveRoot ((((hξ.isUnit hN0).unit ^ ℓg : Lˣ)) : L) q := by
    rw [Units.val_pow_eq_pow_val, hξu]; exact hξ.pow (Nat.pos_of_ne_zero hN0) (Nat.mul_comm q ℓg)
  have hc1 : ((hξ.isUnit hN0).unit ^ q) ^ ℓg = 1 := by
    rw [← pow_mul]; ext; rw [Units.val_pow_eq_pow_val, hξu, Units.val_one]; exact hξ.pow_eq_one
  have hcne : (hξ.isUnit hN0).unit ^ q ≠ 1 := by
    intro h1
    apply hcq.ne_one (by omega)
    rw [h1, Units.val_one]
  have hc2_1 : (((hξ.isUnit hN0).unit ^ q) ^ 2) ^ ℓg = 1 := by
    rw [pow_right_comm, hc1, one_pow]
  have hc2ne : ((hξ.isUnit hN0).unit ^ q) ^ 2 ≠ 1 := by
    intro h1
    apply hcq.pow_ne_one_of_pos_of_lt (by norm_num : (2 : ℕ) ≠ 0) (by omega)
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]

  obtain ⟨⟨xP, hxP⟩, ⟨yP, hyP⟩⟩ := htoric ((hξ.isUnit hN0).unit ^ q) hc1 hcne
  let D₀ : ModularCurve.LevelPData ↥K := ⟨xP, yP, xP, yP⟩
  have hD₀map : D₀.map (algebraMap ↥K (LaurentSeries L)) =
      ((⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit hN0).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit hN0).unit ^ q)).2,
          (ModularCurve.tateToricPoint L q ((hξ.isUnit hN0).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit hN0).unit ^ q)).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange C) := by
    refine ModularCurve.LevelPData.ext hxP hyP ?_ ?_
    · exact hxP
    · exact hyP
  letI algA : Algebra A (LaurentSeries L) := ((algebraMap L (LaurentSeries L)).comp (algebraMap A L)).toAlgebra
  have hTg1 := ModularCurve.isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot L q ℓg hℓg hℓg2 ((hξ.isUnit hN0).unit ^ q) hcq
  have hTg1C := hℓ (LaurentSeries L) (ModularCurve.tateBase L q) C _ hTg1
  have hD₀ : ModularCurve.IsGamma1Point W₀ ℓg D₀ :=
    TPH1Aux.isGamma1Point_of_map (algebraMap ↥K (LaurentSeries L)) (by rw [hW₀, hD₀map]; exact hTg1C)

  have hv : (![(1 : ZMod q), 0] : Fin 2 → ZMod q) ≠ 0 := fun h => by
    have := congrFun h 0; simp at this
  have hw : (![0, -(1 : ZMod q)] : Fin 2 → ZMod q) ≠ 0 := fun h => by
    have := congrFun h 1; simp at this
  obtain ⟨Px, hPx⟩ := (hcusp _ _ hv hw).1
  obtain ⟨Py, hPy⟩ := (hcusp _ _ hv hw).2
  obtain ⟨Qx, hQx⟩ := (hcusp _ _ hw hv).1
  obtain ⟨Qy, hQy⟩ := (hcusp _ _ hw hv).2
  let Dq : ModularCurve.LevelPData ↥K := ⟨Px, Py, Qx, Qy⟩
  have hDqmap : Dq.map (algebraMap ↥K (LaurentSeries L)) =
      (ModularCurve.cuspData L q ((hξ.isUnit hN0).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C := by
    refine ModularCurve.LevelPData.ext hPx hPy ?_ ?_
    · exact hQx
    · exact hQy
  obtain ⟨heqP, heqQ, tP, tQ, hind⟩ :=
    ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData L q ((hξ.isUnit hN0).unit ^ ℓg) hζq C ↥K (algebraMap ↥K (LaurentSeries L)) W₀ Dq hW₀ hDqmap

  obtain ⟨SP, hSP⟩ := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    (W₀ : WeierstrassCurve.Projective ↥K)).1 Px Py).mp heqP
  obtain ⟨SQ, hSQ⟩ := ((WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
    (W₀ : WeierstrassCurve.Projective ↥K)).1 Qx Qy).mp heqQ
  have hqL : IsUnit ((q : ℕ) : L) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hq0)
  have hqK : ((q : ℕ) : ↥K) ≠ 0 := by
    intro h0
    apply hqL.ne_zero
    have := congrArg (algebraMap ↥K (LaurentSeries L)) h0
    rw [map_natCast, map_zero] at this
    have h2 : (algebraMap L (LaurentSeries L)) (q : L) = 0 := by rw [map_natCast]; exact this
    exact (algebraMap L (LaurentSeries L)).injective (by rw [h2, map_zero])
  have hDrin : IsDrinfeldBasis (𝒢 ↥K W₀ hΔ₀) q SP SQ :=
    WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isSectionThrough_of_torsion_basis A 𝒢 h𝒢 h𝒢O
      (W₀ : WeierstrassCurve.Projective ↥K) hΔ₀ q hqK SP SQ Px Py Qx Qy hSP hSQ tP tQ hind

  have hcomp : ∀ p : ↥M'.primeFactors, ∃ h₀ : Polynomial ↥K,
      ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) h₀ ∧
      ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        (h₀.map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1)) := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    haveI : Fact (p : ℕ).Prime := ⟨hp⟩
    have hpL : ((p : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' (p : ℕ)
    obtain ⟨h, hhk, hh⟩ :=
      ModularCurve.exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint L (p : ℕ)
        (M'.factorization (p : ℕ)) hpL q
    have hhC := hM (LaurentSeries L) (ModularCurve.tateBase L q) C (p : ℕ) (M'.factorization (p : ℕ)) h hhk
    have hcoefK :=
      ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_fst_mem_range_rigidDataH1Pow
        q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ hιξ H₁ hH₁ K hK (p : ℕ) (M'.factorization (p : ℕ)) hpk h
        (fun F' _ f ζ' hζ' => hh F' f ζ' hζ') C (htoric _ hc1 hcne).1 (htoric _ hc2_1 hc2ne).1
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : Polynomial ↥K, h₀.map (algebraMap ↥K (LaurentSeries L)) =
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) h := by
      have hl : ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) h ∈
          Polynomial.lifts (algebraMap ↥K (LaurentSeries L)) :=
        (Polynomial.lifts_iff_coeff_lifts _).mpr (fun n => hcoefK n)
      obtain ⟨h₀, hh₀⟩ := RingHom.mem_rangeS.mp hl
      exact ⟨h₀, hh₀⟩
    refine ⟨h₀, TPH1Aux.isGamma0PowAt_of_map (algebraMap ↥K (LaurentSeries L)) (by rw [hW₀, hh₀]; exact hhC), ?_⟩
    intro F' _ f ζ' hζ'
    rw [hh₀, ModularCurve.kernelVariableChangeDeg_map, hh F' f ζ' hζ']
  choose hT hTspec hTtoric using hcomp

  have hLink : ModularCurve.IsGamma1Link W₀ ℓg M' hT D₀ := by
    intro hmem
    have hk : 1 ≤ M'.factorization ℓg := (Nat.Prime.factorization_pos_of_dvd hℓg (NeZero.ne M') hℓgM')
    exact ModularCurve.dvd_inLineMulPoly_of_map_eq_variableChange_tateBase_tateToricPoint_of_map_eq_kernelVariableChangeDeg L q ℓg hℓg hℓg2 (M'.factorization ℓg) hk
      ((hξ.isUnit hN0).unit ^ q) hcq C ↥K (algebraMap ↥K (LaurentSeries L)) W₀ D₀ (hT ⟨ℓg, hmem⟩) hW₀ hD₀map
      (fun F' _ f ζ' hζ' => hTtoric ⟨ℓg, hmem⟩ F' f ζ' hζ')

  refine ⟨C, ⟨W₀, hΔ₀, (hT, (D₀, ⟨W₀, SP, SQ⟩)), ⟨⟨hTspec, hD₀, rfl, hΔ₀, hDrin⟩, hLink⟩⟩, ⟨hu, hr, hs, ht⟩, hW₀,
    (fun p F' _ f ζ' hζ' => hTtoric p F' f ζ' hζ'), hD₀map,
    ⟨Px, Py, Qx, Qy, hPx, hPy, hQx, hQy, hSP, hSQ⟩, ?_⟩

  have key : ∀ (W' : WeierstrassCurve (LaurentSeries L)) (h' : IsUnit W'.Δ),
      W' = C • ModularCurve.tateBase L q → W'.jOfUnit h' = ModularCurve.jqNModC L q := by
    intro W' h' e
    subst e
    rw [(ModularCurve.tateBase L q).jOfUnit_variableChange C (ModularCurve.isUnit_Δ_tateBase L q) h']
    show ((ModularCurve.tateLaurent L).map (ModularCurve.qExpand L q)).jOfUnit (ModularCurve.isUnit_Δ_tateBase L q) =
      ModularCurve.qExpand L q (ModularCurve.jqModC L)
    rw [(ModularCurve.tateLaurent L).jOfUnit_map (ModularCurve.qExpand L q) (ModularCurve.tateLaurent L).isUnit_Δ
      (ModularCurve.isUnit_Δ_tateBase L q), WeierstrassCurve.jOfUnit_eq_j, ModularCurve.j_tateLaurent]
  have key2 : ∀ (V : WeierstrassCurve ↥K) (hV : IsUnit V.Δ), V = W₀ →
      ((V.jOfUnit hV : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q := by
    intro V hV e
    subst e
    show algebraMap ↥K (LaurentSeries L) (W₀.jOfUnit hV) = _
    rw [← W₀.jOfUnit_map (algebraMap ↥K (LaurentSeries L)) hV (W₀.isUnit_Δ_map _ hV)]
    exact key _ _ hW₀
  dsimp only [ModularCurve.RigidWeierstrassData.toLevelModuliDatum]
  rw [ModularCurve.RigidWeierstrassData.jOf_mk]
  exact key2 _ _ rfl

end S_ModularCurve_FullLevel_Diamond_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_raw_rigidData_tate_weightOne_level_fst_rigidDataH1Pow (solution)
