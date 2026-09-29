-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_represents_raw_rigidData_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a163125f-1e1f-5458-85ff-98de3c410aa2

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr
import Theorems.Thm_ModularCurve_LevelP_BasisRing_etale
import Theorems.Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq
import Theorems.Thm_ModularCurve_LevelP_BasisRing_ringHom_ext_of_basisData_map_eq
import Theorems.Thm_ModularCurve_IsGamma0PowAt_exists_moduleFinite_represents_tuple
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_moduleFinite_represents_isLevel
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_represents_raw_rigidData_gamma0Pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem solution
    (A : Type u) [CommRing A] (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'u : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (xᵤ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T),
        ∃! ψ : C →ₐ[A] T, (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ψ xᵤ = x := by
  classical

  obtain ⟨S₀, _, _, _, W0, hΔ0, hunivW⟩ := WeierstrassCurve.exists_finiteType_universal_of_isUnit_discr A

  let R₁ : Type u := ModularCurve.LevelP.BasisRing W0 ℓ
  letI : Algebra A R₁ := ((algebraMap S₀ R₁).comp (algebraMap A S₀)).toAlgebra
  haveI : IsScalarTower A S₀ R₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hℓ2 : ℓ ≠ 2 := by omega
  have hℓodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  have hℓS₀ : IsUnit ((ℓ : ℕ) : S₀) := by simpa using hℓA.map (algebraMap A S₀)
  have hℓΔ : IsUnit (((ℓ : ℕ) : S₀) * W0.Δ) := hℓS₀.mul hΔ0
  haveI : Algebra.Etale S₀ R₁ := ModularCurve.LevelP.BasisRing.etale W0 hℓodd hℓΔ
  haveI : Algebra.FiniteType A R₁ := Algebra.FiniteType.trans (S := S₀) inferInstance inferInstance
  let W₁ : WeierstrassCurve R₁ := ModularCurve.LevelP.basisCurve W0 ℓ
  have hΔ₁ : IsUnit W₁.Δ := ModularCurve.LevelP.isUnit_Δ_basisCurve W0 ℓ hΔ0
  let D₁ : ModularCurve.LevelPData R₁ := ModularCurve.LevelP.basisData W0 ℓ
  have hD₁ : ModularCurve.IsLevelPStructure W₁ ℓ D₁ := ModularCurve.LevelP.isLevelPStructure_basisData W0 ℓ

  have hMR₁ : IsUnit ((M' : ℕ) : R₁) := by simpa using hM'u.map (algebraMap A R₁)
  have hMΔ : IsUnit (((M' : ℕ) : R₁) * W₁.Δ) := hMR₁.mul hΔ₁
  obtain ⟨C₂, _, _, _, hK, hhK, hunivK⟩ :=
    ModularCurve.IsGamma0PowAt.exists_moduleFinite_represents_tuple W₁ M' hMΔ
  letI : Algebra A C₂ := ((algebraMap R₁ C₂).comp (algebraMap A R₁)).toAlgebra
  haveI : IsScalarTower A R₁ C₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A C₂ := Algebra.FiniteType.trans (S := R₁) inferInstance inferInstance
  let W₂ : WeierstrassCurve C₂ := W₁.map (algebraMap R₁ C₂)
  have hΔ₂ : IsUnit W₂.Δ := W₁.isUnit_Δ_map (algebraMap R₁ C₂) hΔ₁

  have hVC' : ∀ (T : Type u) [CommRing T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ), IsVariableChangeHom W C φ := by
    intro T _ W C
    obtain ⟨φ, hφ, hV, -, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap W C
    exact ⟨φ, hφ, hV⟩
  have hCO' : ∀ (T T' : Type u) [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T'),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ), IsCoefficientHom W f φ :=
    fun T T' _ _ W f => WeierstrassProjModel.exists_isCoefficientHom W f
  obtain ⟨C₃, _, _, _, _, _, zD, hzD, hunivD⟩ :=
    WeierstrassCurve.DrinfeldGlobal.exists_moduleFinite_represents_isLevel q 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC' hCO' C₂ W₂ hΔ₂
  haveI : Algebra.FiniteType A C₃ := Algebra.FiniteType.trans (S := C₂) inferInstance inferInstance

  let W₃ : WeierstrassCurve C₃ := W₂.map (algebraMap C₂ C₃)
  have hΔ₃ : IsUnit W₃.Δ := W₂.isUnit_Δ_map (algebraMap C₂ C₃) hΔ₂
  let h₃ : ↥M'.primeFactors → Polynomial C₃ := fun p => (hK p).map (algebraMap C₂ C₃)
  have hh₃ : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W₃ (p : ℕ) (M'.factorization (p : ℕ)) (h₃ p) :=
    fun p => ModularCurve.IsGamma0PowAt.map (algebraMap C₂ C₃) W₂ (p : ℕ) _ (hhK p)
  let D₃ : ModularCurve.LevelPData C₃ := (D₁.map (algebraMap R₁ C₂)).map (algebraMap C₂ C₃)
  have hD₃ : ModularCurve.IsLevelPStructure W₃ ℓ D₃ := (hD₁.map (algebraMap R₁ C₂)).map (algebraMap C₂ C₃)
  refine ⟨C₃, inferInstance, inferInstance, inferInstance, ⟨W₃, hΔ₃, ⟨h₃, D₃, zD⟩, ⟨hh₃, hD₃, hzD⟩⟩, ?_⟩
  intro T _ _ x
  obtain ⟨W, hΔ, ⟨h, D, z⟩, ⟨hh, hD, hz⟩⟩ := x

  have alg₀₁ : algebraMap S₀ R₁ = ModularCurve.LevelP.BasisRing.ofBase W0 ℓ := rfl
  have hW₁def : W₁ = W0.map (algebraMap S₀ R₁) := rfl

  obtain ⟨ψ₀, hψ₀W, huniq₀⟩ := hunivW T W hΔ

  have hD' : ModularCurve.IsLevelPStructure (W0.map ψ₀.toRingHom) ℓ D := by rw [hψ₀W]; exact hD
  obtain ⟨ψ₁, hψ₁c, hψ₁D⟩ :=
    ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq W0 ℓ ψ₀.toRingHom D hD'
  have hW₁ : W₁.map ψ₁ = W := by
    rw [hW₁def, WeierstrassCurve.map_map, alg₀₁, hψ₁c, hψ₀W]

  have hhK' : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt (W₁.map ψ₁) (p : ℕ) (M'.factorization (p : ℕ)) (h p) := by
    rw [hW₁]; exact hh
  obtain ⟨ψ₂, ⟨hψ₂c, hψ₂h⟩, huniq₂⟩ := (hunivK T ψ₁ h).mp hhK'
  have hψ₂A : ∀ a, ψ₂ (algebraMap A C₂ a) = algebraMap A T a := fun a => by
    show ψ₂ (algebraMap R₁ C₂ (algebraMap S₀ R₁ (algebraMap A S₀ a))) = algebraMap A T a
    rw [← RingHom.comp_apply ψ₂, hψ₂c, alg₀₁, ← RingHom.comp_apply ψ₁, hψ₁c]
    exact ψ₀.commutes a
  let φ₂ : C₂ →ₐ[A] T := { toRingHom := ψ₂, commutes' := hψ₂A }
  have hW₂ : W₂.map φ₂.toRingHom = W := by
    show (W₁.map (algebraMap R₁ C₂)).map ψ₂ = W
    rw [WeierstrassCurve.map_map, hψ₂c, hW₁]

  have hz' : RawDrinfeldPair.IsLevel 𝒢 q (W₂.map φ₂.toRingHom) z := by rw [hW₂]; exact hz
  obtain ⟨ψ₃, ⟨hψ₃c, hψ₃z⟩, huniq₃⟩ := (hunivD T φ₂ z).mp hz'
  have hψ₃c' : ψ₃.toRingHom.comp (algebraMap C₂ C₃) = ψ₂ := hψ₃c
  refine ⟨ψ₃, ?_, ?_⟩
  ·
    refine ModularCurve.LevelComponent.Raw.ext' ?_ ?_
    · show W₃.map ψ₃.toRingHom = W
      show ((W₁.map (algebraMap R₁ C₂)).map (algebraMap C₂ C₃)).map ψ₃.toRingHom = W
      rw [WeierstrassCurve.map_map, hψ₃c', WeierstrassCurve.map_map, hψ₂c, hW₁]
    · show ((fun p : ↥M'.primeFactors => (h₃ p).map ψ₃.toRingHom), D₃.map ψ₃.toRingHom, 𝒯.map ψ₃ zD) = (h, D, z)
      refine Prod.ext ?_ (Prod.ext ?_ hψ₃z)
      · show (fun p : ↥M'.primeFactors => ((hK p).map (algebraMap C₂ C₃)).map ψ₃.toRingHom) = h
        rw [← hψ₂h]
        funext p
        rw [Polynomial.map_map, hψ₃c']
      · show ((D₁.map (algebraMap R₁ C₂)).map (algebraMap C₂ C₃)).map ψ₃.toRingHom = D
        rw [ModularCurve.LevelPData.map_map, hψ₃c', ModularCurve.LevelPData.map_map, hψ₂c, hψ₁D]
  ·
    intro ψ' hψ'
    have hc : W₃.map ψ'.toRingHom = W := congrArg ModularCurve.LevelComponent.Raw.curve hψ'
    have hl : ((fun p : ↥M'.primeFactors => (h₃ p).map ψ'.toRingHom), D₃.map ψ'.toRingHom, 𝒯.map ψ' zD) = (h, D, z) :=
      congrArg ModularCurve.LevelComponent.Raw.level hψ'
    have hl₁ : (fun p : ↥M'.primeFactors => (h₃ p).map ψ'.toRingHom) = h := congrArg Prod.fst hl
    have hl₂ : D₃.map ψ'.toRingHom = D := congrArg (fun t => t.2.1) hl
    have hl₃ : 𝒯.map ψ' zD = z := congrArg (fun t => t.2.2) hl

    let φ₂' : C₂ →ₐ[A] T := ψ'.comp (IsScalarTower.toAlgHom A C₂ C₃)
    have hφ₂' : φ₂'.toRingHom = ψ'.toRingHom.comp (algebraMap C₂ C₃) := rfl
    let ψ₁' : R₁ →+* T := φ₂'.toRingHom.comp (algebraMap R₁ C₂)
    let ψ₀' : S₀ →ₐ[A] T := (φ₂'.comp (IsScalarTower.toAlgHom A R₁ C₂)).comp (IsScalarTower.toAlgHom A S₀ R₁)
    have hψ₀'r : ψ₀'.toRingHom = ψ₁'.comp (algebraMap S₀ R₁) := rfl

    have h0 : ψ₀' = ψ₀ := by
      apply huniq₀
      rw [hψ₀'r]
      show W0.map ((ψ'.toRingHom.comp (algebraMap C₂ C₃)).comp (algebraMap R₁ C₂) |>.comp (algebraMap S₀ R₁)) = W
      rw [← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map, ← WeierstrassCurve.map_map]
      exact hc

    have h1 : ψ₁' = ψ₁ := by
      apply ModularCurve.LevelP.BasisRing.ringHom_ext_of_basisData_map_eq W0 ℓ ψ₀.toRingHom ψ₁' ψ₁ _ hψ₁c
      · rw [hψ₁D]
        show ((ModularCurve.LevelP.basisData W0 ℓ).map ((ψ'.toRingHom.comp (algebraMap C₂ C₃)).comp (algebraMap R₁ C₂))) = D
        rw [← ModularCurve.LevelPData.map_map, ← ModularCurve.LevelPData.map_map]
        exact hl₂
      · rw [← alg₀₁, ← hψ₀'r, h0]

    have h2 : φ₂'.toRingHom = ψ₂ := by
      apply huniq₂
      refine ⟨h1, ?_⟩
      rw [← hl₁]
      funext p
      show (hK p).map (ψ'.toRingHom.comp (algebraMap C₂ C₃)) = ((hK p).map (algebraMap C₂ C₃)).map ψ'.toRingHom
      rw [Polynomial.map_map]

    apply huniq₃
    exact ⟨h2, hl₃⟩

end S_ModularCurve_FullLevel_exists_represents_raw_rigidData_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_represents_raw_rigidData_gamma0Pow (solution)
