-- Prove2me | solution 1 for ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/010b8b7d-3aae-5ad9-a485-b0d47a8d2ded

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace DiaExH

section Restrict

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  (F₀ F₁ : IntermediateField K E) (hle : F₀ ≤ F₁) (σ : F₁ ≃ₐ[K] F₁)
  (hσ : ∀ y : F₁, (y : E) ∈ F₀ → ((σ y : F₁) : E) ∈ F₀)
  (hσ' : ∀ y : F₁, (y : E) ∈ F₀ → ((σ.symm y : F₁) : E) ∈ F₀)

def restrictHom : F₀ →ₐ[K] F₀ :=
  (F₁.val.comp ((σ : F₁ →ₐ[K] F₁).comp (IntermediateField.inclusion hle))).codRestrict
    F₀.toSubalgebra (fun x => hσ _ x.2)

theorem coe_restrictHom_apply (x : F₀) :
    ((restrictHom F₀ F₁ hle σ hσ x : F₀) : E) = ((σ (IntermediateField.inclusion hle x) : F₁) : E) :=
  rfl

include hσ' in
theorem restrictHom_bijective : Function.Bijective (restrictHom F₀ F₁ hle σ hσ) := by
  refine ⟨(restrictHom F₀ F₁ hle σ hσ).injective, fun y => ?_⟩
  refine ⟨⟨((σ.symm (IntermediateField.inclusion hle y) : F₁) : E), hσ' _ y.2⟩, ?_⟩
  apply Subtype.ext
  rw [coe_restrictHom_apply]
  have e : IntermediateField.inclusion hle
      ⟨((σ.symm (IntermediateField.inclusion hle y) : F₁) : E), hσ' _ y.2⟩
        = σ.symm (IntermediateField.inclusion hle y) := Subtype.ext rfl
  rw [e, AlgEquiv.apply_symm_apply]
  rfl

def restrictAut : F₀ ≃ₐ[K] F₀ :=
  AlgEquiv.ofBijective (restrictHom F₀ F₁ hle σ hσ) (restrictHom_bijective F₀ F₁ hle σ hσ hσ')

theorem coe_restrictAut_apply (x : F₀) :
    ((restrictAut F₀ F₁ hle σ hσ hσ' x : F₀) : E) = ((σ (IntermediateField.inclusion hle x) : F₁) : E) := by
  rw [restrictAut, AlgEquiv.ofBijective_apply, coe_restrictHom_apply]

variable {G : Type*} [Group G] (ρ : G →* (F₁ ≃ₐ[K] F₁))
  (hρ : ∀ (g : G) (y : F₁), (y : E) ∈ F₀ → ((ρ g y : F₁) : E) ∈ F₀)

include hρ in

theorem stable_symm (g : G) (y : F₁) (hy : (y : E) ∈ F₀) : (((ρ g).symm y : F₁) : E) ∈ F₀ := by
  have := hρ g⁻¹ y hy
  rwa [map_inv] at this

def restrictAction : G →* (F₀ ≃ₐ[K] F₀) where
  toFun g := restrictAut F₀ F₁ hle (ρ g) (hρ g) (stable_symm F₀ F₁ ρ hρ g)
  map_one' := by
    apply AlgEquiv.ext; intro x; apply Subtype.ext
    rw [coe_restrictAut_apply, map_one, AlgEquiv.one_apply, AlgEquiv.one_apply,
      IntermediateField.coe_inclusion]
  map_mul' g g' := by
    apply AlgEquiv.ext; intro x; apply Subtype.ext
    rw [coe_restrictAut_apply, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, coe_restrictAut_apply]
    have e : IntermediateField.inclusion hle
        (restrictAut F₀ F₁ hle (ρ g') (hρ g') (stable_symm F₀ F₁ ρ hρ g') x)
          = ρ g' (IntermediateField.inclusion hle x) :=
      Subtype.ext (coe_restrictAut_apply F₀ F₁ hle (ρ g') (hρ g') (stable_symm F₀ F₁ ρ hρ g') x)
    rw [e]

theorem coe_restrictAction_apply (g : G) (x : F₀) :
    ((restrictAction F₀ F₁ hle ρ hρ g x : F₀) : E) = ((ρ g (IntermediateField.inclusion hle x) : F₁) : E) := by
  rw [restrictAction, MonoidHom.coe_mk, OneHom.coe_mk, coe_restrictAut_apply]

end Restrict

variable {K : Type*} [Field K] {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem inv_mul_mul_mem_GammaH (γ : Gamma0 M) {δ : SL(2, ℤ)} (hδ : δ ∈ CohCarrier.GammaH M H) :
    (γ : SL(2, ℤ))⁻¹ * δ * (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H := by
  have := CohCarrier.conj_mem_GammaH M H γ⁻¹ ⟨δ, hδ⟩
  simpa using this

theorem stable_of_gal
    (ρ : Gamma0 M →*
      (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)))
    (hgal : ∀ (H : Subgroup (ZMod M)ˣ) (y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
      (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) ↔
        ∀ γ : Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y)
    (γ : Gamma0 M) (y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))
    (hy : (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H)) :
    ((ρ γ y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) : LaurentSeries K) ∈
      qExpFunctionFieldC K (CohCarrier.GammaH M H) := by
  rw [hgal H] at hy ⊢
  intro δ hδ
  have h1 : ρ δ (ρ γ y) = ρ γ (ρ (γ⁻¹ * δ * γ) y) := by
    rw [← AlgEquiv.mul_apply, ← map_mul, ← AlgEquiv.mul_apply, ← map_mul, mul_assoc,
      mul_inv_cancel_left]
  rw [h1, hy (γ⁻¹ * δ * γ) (inv_mul_mul_mem_GammaH γ hδ)]

end DiaExH

open DiaExH in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
          ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      ModularCurve.IsDiamondPullbackModL K M H ρ := by
  obtain ⟨ρ, hρ, hgal⟩ := ModularCurve.exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff K M hM
  have hle : qExpFunctionFieldC K (CohCarrier.GammaH M H) ≤ qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) :=
    qExpFunctionFieldC_mono K (GammaH_mono bot_le)
  refine ⟨restrictAction (qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) hle ρ (stable_of_gal ρ hgal), ?_⟩

  intro γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg x hx
  have hle' : ((CohCarrier.GammaH M ⊥ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (GammaH_mono bot_le)
  have hf' : IsIntegralQExp (restrictForm hle' f) pf := by rw [IsIntegralQExp, coe_restrictForm]; exact hf
  have hg' : IsIntegralQExp (restrictForm hle' g) pg := by rw [IsIntegralQExp, coe_restrictForm]; exact hg
  have hf₁' : IsIntegralQExp (restrictForm hle' f₁) pf₁ := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hf₁
  have hg₁' : IsIntegralQExp (restrictForm hle' g₁) pg₁ := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hg₁
  have hfs' : (⇑(restrictForm hle' f₁) : UpperHalfPlane → ℂ) =
      ((⇑(restrictForm hle' f) : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
    rw [coe_restrictForm, coe_restrictForm]; exact hfs
  have hgs' : (⇑(restrictForm hle' g₁) : UpperHalfPlane → ℂ) =
      ((⇑(restrictForm hle' g) : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) := by
    rw [coe_restrictForm, coe_restrictForm]; exact hgs
  have hx' : ((IntermediateField.inclusion hle x : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) :
      LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁ := by
    rw [IntermediateField.coe_inclusion]; exact hx
  have key := hρ γ k (restrictForm hle' f) (restrictForm hle' g) (restrictForm hle' f₁)
    (restrictForm hle' g₁) pf pg pf₁ pg₁ hf' hg' hf₁' hg₁' hfs' hgs' hpg (IntermediateField.inclusion hle x) hx'
  exact (coe_restrictAction_apply (qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)) hle ρ (stable_of_gal ρ hgal) γ x).trans key

end
end S_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed (solution)
