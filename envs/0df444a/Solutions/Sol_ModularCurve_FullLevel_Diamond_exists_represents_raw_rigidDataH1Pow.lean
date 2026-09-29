-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/dc773a2d-3bcd-57e5-9040-d31f59bf5e3a

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataGamma1Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem solution
    (A : Type u) [CommRing A] (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'u : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
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
      (xᵤ : (rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯).Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (x : (rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯).Raw T),
        ∃! ψ : C →ₐ[A] T, (rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯).mapRing ψ xᵤ = x := by
  classical
  obtain ⟨C, _, _, _, xu, huniv⟩ :=
    ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataGamma1Pow A q ℓ M' hℓ3 hℓA hM'u hℓ hM 𝒢 h𝒢 h𝒢O
      𝒯 h𝒯 hVC hCO

  let R : ModularCurve.RigidWeierstrassData.{u} A := rigidDataGamma1Pow A ℓ M' q hℓ hM 𝒢 𝒯
  let L : ModularCurve.LevelComponent A :=
    (ModularCurve.gamma0PowComponent A M' hM).prod
      ((ModularCurve.gamma1Component A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))
  let RH : ModularCurve.RigidWeierstrassData.{u} A := rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯
  obtain ⟨Wu, hΔu, levu, hlevu⟩ := xu
  obtain ⟨hu, Du, zu⟩ := levu

  let n : ℕ := ℓ ^ (M'.factorization ℓ - 1)
  let F : Polynomial C := ModularCurve.inLineMulPoly Wu ℓ n Du.xP
  have hne2 : ℓ ^ (M'.factorization ℓ) ≠ 2 := by
    intro h2
    rcases Nat.eq_zero_or_pos (M'.factorization ℓ) with hk | hk
    · rw [hk, pow_zero] at h2; omega
    · have : ℓ ≤ ℓ ^ (M'.factorization ℓ) := Nat.le_self_pow hk.ne' ℓ
      omega
  have hmon : ∀ hmem : ℓ ∈ M'.primeFactors, (hu ⟨ℓ, hmem⟩).Monic := fun hmem =>
    ((ModularCurve.isGamma0PowAt_of_pow_ne_two Wu hne2 _).1 (hlevu.1 ⟨ℓ, hmem⟩)).monic
  let r : Polynomial C := if hmem : ℓ ∈ M'.primeFactors then F %ₘ (hu ⟨ℓ, hmem⟩) else 0
  let I : Ideal C := Ideal.span (Set.range r.coeff)

  have hkill : ∀ {T : Type u} [CommRing T] (g : C →+* T),
      (∀ i, g (r.coeff i) = 0) ↔
        ∀ hmem : ℓ ∈ M'.primeFactors, (hu ⟨ℓ, hmem⟩).map g ∣ F.map g := by
    intro T _ g
    have hr : (∀ i, g (r.coeff i) = 0) ↔ r.map g = 0 := by
      rw [Polynomial.ext_iff]; simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    rw [hr]
    by_cases hmem : ℓ ∈ M'.primeFactors
    · have hrdef : r = F %ₘ (hu ⟨ℓ, hmem⟩) := dif_pos hmem
      rw [hrdef, Polynomial.map_modByMonic g (hmon hmem),
        Polynomial.modByMonic_eq_zero_iff_dvd ((hmon hmem).map g)]
      exact ⟨fun h _ => h, fun h => h hmem⟩
    · have hrdef : r = 0 := dif_neg hmem
      rw [hrdef, Polynomial.map_zero]
      exact ⟨fun _ h => (hmem h).elim, fun _ => rfl⟩

  let C' : Type u := C ⧸ I
  let π : C →ₐ[A] C' := Ideal.Quotient.mkₐ A I
  haveI : Algebra.FiniteType A C' :=
    Algebra.FiniteType.of_surjective π (Ideal.Quotient.mkₐ_surjective A I)
  have hπ0 : ∀ i, π.toRingHom (r.coeff i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)

  let y : R.Raw C' := R.mapRing π ⟨Wu, hΔu, (hu, Du, zu), hlevu⟩
  have hylink : ModularCurve.IsGamma1Link y.curve ℓ M' y.level.1 y.level.2.1 := by
    intro hmem
    show (hu ⟨ℓ, hmem⟩).map π.toRingHom ∣
      ModularCurve.inLineMulPoly (Wu.map π.toRingHom) ℓ n (Du.map π.toRingHom).xP
    rw [ModularCurve.LevelPData.map_xP, ModularCurve.inLineMulPoly_map]
    exact (hkill π.toRingHom).1 hπ0 hmem
  let xu' : RH.Raw C' := ⟨y.curve, y.isUnit_Δ, y.level, ⟨y.isLevel, hylink⟩⟩
  refine ⟨C', inferInstance, inferInstance, inferInstance, xu', ?_⟩
  intro T _ _ x
  obtain ⟨W, hΔ, lev, ⟨hlev, hlk⟩⟩ := x
  let x₀ : R.Raw T := ⟨W, hΔ, lev, hlev⟩
  obtain ⟨ψ, hψ, hψuniq⟩ := huniv T x₀
  have hc : Wu.map ψ.toRingHom = W := congrArg ModularCurve.LevelComponent.Raw.curve hψ
  have hl : L.map ψ (hu, Du, zu) = lev := congrArg ModularCurve.LevelComponent.Raw.level hψ

  have hψI : ∀ i, ψ.toRingHom (r.coeff i) = 0 := by
    refine (hkill ψ.toRingHom).2 fun hmem => ?_
    have h1 := hlk hmem
    rw [← hc, ← hl] at h1
    change (hu ⟨ℓ, hmem⟩).map ψ.toRingHom ∣
      ModularCurve.inLineMulPoly (Wu.map ψ.toRingHom) ℓ n (Du.map ψ.toRingHom).xP at h1
    rwa [ModularCurve.LevelPData.map_xP, ModularCurve.inLineMulPoly_map] at h1
  have hIker : ∀ a : C, a ∈ I → ψ a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker ψ.toRingHom := Ideal.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact hψI i)
    exact hle ha
  let ψ' : C' →ₐ[A] T := Ideal.Quotient.liftₐ I ψ hIker
  have hψ'π : ψ'.comp π = ψ := Ideal.Quotient.liftₐ_comp I ψ hIker
  have hψ'πr : ψ'.toRingHom.comp π.toRingHom = ψ.toRingHom := congrArg AlgHom.toRingHom hψ'π
  refine ⟨ψ', ?_, ?_⟩
  · refine ModularCurve.LevelComponent.Raw.ext' ?_ ?_
    · show (Wu.map π.toRingHom).map ψ'.toRingHom = W
      rw [WeierstrassCurve.map_map, hψ'πr, hc]
    · show L.map ψ' (L.map π (hu, Du, zu)) = lev
      rw [← L.map_comp, hψ'π, hl]
  · intro φ hφ
    apply Ideal.Quotient.algHom_ext
    rw [hψ'π]
    apply hψuniq
    show R.mapRing (φ.comp π) ⟨Wu, hΔu, (hu, Du, zu), hlevu⟩ = x₀
    rw [R.mapRing_comp]
    have hc' : (Wu.map π.toRingHom).map φ.toRingHom = W :=
      congrArg ModularCurve.LevelComponent.Raw.curve hφ
    have hl' : L.map φ (L.map π (hu, Du, zu)) = lev :=
      congrArg ModularCurve.LevelComponent.Raw.level hφ
    exact ModularCurve.LevelComponent.Raw.ext' hc' hl'

end S_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataH1Pow (solution)
