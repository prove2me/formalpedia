-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b9ea0bf1-5e47-55c9-9deb-6c4d641e2d56

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

noncomputable section

namespace WChart

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj)

local notation "𝕂" => AlgebraicClosure ℚ

abbrev Xbar : Scheme.{0} :=
  pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) 𝕂)))

def wBar : Xbar (p := p) (M := M) (H := H) (hj := hj) ⟶ Xbar (p := p) (M := M) (H := H) (hj := hj) :=
  pullback.map _ _ _ _ 𝔓.w.hom (𝟙 _) (𝟙 _)
    (by rw [𝔓.w_over, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

scoped instance isIso_wBar : IsIso (wBar 𝔓) := by
  unfold wBar; infer_instance

@[reassoc] theorem wBar_fst : wBar 𝔓 ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔓.w.hom := by
  unfold wBar; exact pullback.lift_fst _ _ _

@[reassoc] theorem wBar_snd : wBar 𝔓 ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold wBar; rw [pullback.lift_snd, Category.comp_id]

def omega : 𝔓.Meta.C ⟶ 𝔓.Meta.C :=
  haveI := 𝔓.eeta_iso
  𝔓.eeta ≫ wBar 𝔓 ≫ inv 𝔓.eeta

scoped instance isIso_omega : IsIso (omega 𝔓) := by
  haveI := 𝔓.eeta_iso
  unfold omega; infer_instance

theorem omega_eeta : omega 𝔓 ≫ 𝔓.eeta = 𝔓.eeta ≫ wBar 𝔓 := by
  haveI := 𝔓.eeta_iso
  simp [omega]

theorem omega_e : omega 𝔓 ≫ 𝔓.eeta ≫ pullback.fst _ _ = 𝔓.eeta ≫ pullback.fst _ _ ≫ 𝔓.w.hom := by
  rw [← Category.assoc, omega_eeta, Category.assoc, wBar_fst]

theorem omega_toBase : omega 𝔓 ≫ 𝔓.Meta.toBase = 𝔓.Meta.toBase := by
  rw [← 𝔓.heeta, ← Category.assoc, omega_eeta, Category.assoc, wBar_snd]

def translate (x : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _}) :
    {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _} :=
  ⟨x.1 ≫ omega 𝔓, by rw [Category.assoc, omega_toBase]; exact x.2⟩

theorem pointEquivPlace_eq_smul_translate
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[𝕂] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ ≫ 𝔓.w.hom = y.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ →
        𝔓.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔓.Meta.pointEquivPlace y)
    (x : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _}) :
    𝔓.Meta.pointEquivPlace x = SemilinearAut.ofAlgAut θ • 𝔓.Meta.pointEquivPlace (translate 𝔓 x) := by
  refine hwgen (translate 𝔓 x) x ?_
  show x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ ≫ 𝔓.w.hom = (x.1 ≫ omega 𝔓) ≫ 𝔓.eeta ≫ pullback.fst _ _
  rw [Category.assoc, omega_e]

variable (ρ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂)

def liftBar : Spec (CommRingCat.of 𝕂) ⟶ Xbar (p := p) (M := M) (H := H) (hj := hj) :=
  pullback.lift (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ιFin p (ΓM M H) hj) (𝟙 _) (by
    rw [Category.assoc, TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Category.id_comp]
    congr 2
    exact RingHom.ext fun r => ρ.commutes r)

@[reassoc (attr := simp)] theorem liftBar_fst :
    liftBar ρ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ιFin p (ΓM M H) hj :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem liftBar_snd : liftBar (p := p) (M := M) (H := H) (hj := hj) ρ ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

private def _root_.WChart.lift : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _} :=
  haveI := 𝔓.eeta_iso
  ⟨liftBar ρ ≫ inv 𝔓.eeta, by rw [← 𝔓.heeta, Category.assoc, IsIso.inv_hom_id_assoc, liftBar_snd]⟩

p2m_export "WChart" "lift"
theorem lift_eeta : (lift 𝔓 ρ).1 ≫ 𝔓.eeta = liftBar ρ := by
  haveI := 𝔓.eeta_iso
  show (liftBar ρ ≫ inv 𝔓.eeta) ≫ 𝔓.eeta = liftBar ρ
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

abbrev precomp (τ : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)) :
    ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂 :=
  ρ.comp (τ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))

theorem translate_lift_eeta : (translate 𝔓 (lift 𝔓 ρ)).1 ≫ 𝔓.eeta = liftBar ρ ≫ wBar 𝔓 := by
  show ((lift 𝔓 ρ).1 ≫ omega 𝔓) ≫ 𝔓.eeta = liftBar ρ ≫ wBar 𝔓
  rw [Category.assoc, omega_eeta, ← Category.assoc, lift_eeta]

end WChart
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart"

noncomputable section

namespace WChart

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj)

local notation "𝕂" => AlgebraicClosure ℚ

def bhat (b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(xHFunctionFieldBar M H) :=
  ⟨coeffEmb 𝕂 ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange 𝕂 (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩

def ahat (a : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(xHFunctionFieldBar M H) :=
  ⟨coeffEmb 𝕂 ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange 𝕂 (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩

theorem ahat_jChartFin_mul_bhat_jInvChartInf :
    ahat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) * bhat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) = 1 := by
  apply Subtype.ext
  show coeffEmb 𝕂 ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) *
      coeffEmb 𝕂 (((jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = 1
  have hne : (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≠ 0 := Fact.out
  have h1 : ((jAt (ΓM M H) hj * (jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) *
        (((jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := rfl
  rw [← map_mul, ← h1, mul_inv_cancel₀ hne]
  show coeffEmb 𝕂 (1 : LaurentSeries ℚ) = 1
  exact map_one _

theorem bhat_jInvChartInf_mul_ahat_jChartFin :
    bhat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) *
      ahat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) = 1 := by
  rw [mul_comm]
  exact ahat_jChartFin_mul_bhat_jInvChartInf

variable (P : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})

theorem val_eeta_fst_toBase :
    (P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) 𝕂)) := by
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔓.eeta, 𝔓.heeta, ← Category.assoc, P.2,
    Category.id_comp]

theorem exists_eq_lift_of_comp_eq (z : Spec (CommRingCat.of 𝕂) ⟶ TwoChartIntegralModel.XFin (R p) _ (jAt (ΓM M H) hj))
    (hz : P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = z ≫ ιFin p (ΓM M H) hj) :
    ∃ χ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂, P = WChart.lift 𝔓 χ := by
  haveI := 𝔓.eeta_iso
  set r : ↥(chartAlgFin p (ΓM M H) hj) →+* 𝕂 := (Spec.preimage z).hom with hr
  have hzr : z = Spec.map (CommRingCat.ofHom r) := by
    rw [hr, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hcomm : r.comp (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)) = algebraMap (R p) 𝕂 := by
    have h1 := val_eeta_fst_toBase 𝔓 P
    rw [hz, Category.assoc, hzr] at h1
    erw [TwoChartIntegralModel.ιFin_toBase] at h1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  let χ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂 :=
    { toRingHom := r, commutes' := fun c => RingHom.congr_fun hcomm c }
  refine ⟨χ, ?_⟩
  apply Subtype.ext
  have key : P.1 ≫ 𝔓.eeta = (WChart.lift 𝔓 χ).1 ≫ 𝔓.eeta := by
    rw [WChart.lift_eeta]
    apply pullback.hom_ext
    · rw [Category.assoc, hz, WChart.liftBar_fst, hzr]
    · rw [Category.assoc, 𝔓.heeta, P.2, WChart.liftBar_snd]
  exact (cancel_mono 𝔓.eeta).mp key

theorem place_eq_pointEquivPlace_lift_of_forall_hasValue
    (hread : ∀ (χ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂) (a : ↥(chartAlgFin p (ΓM M H) hj)),
      (𝔓.Meta.pointEquivPlace (WChart.lift 𝔓 χ)).HasValue (ahat a) (χ a))
    (hreadInf : ∀ (Q : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
      (r' : ↥(chartAlgInf p (ΓM M H) hj) →+* 𝕂),
      Q.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom r') ≫ ιInf p (ΓM M H) hj →
        (𝔓.Meta.pointEquivPlace Q).HasValue (bhat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) (r' (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))))
    (χ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂) (w : Place 𝕂 ↥(xHFunctionFieldBar M H))
    (hw : ∀ a : ↥(chartAlgFin p (ΓM M H) hj), w.HasValue (ahat a) (χ a)) :
    w = 𝔓.Meta.pointEquivPlace (WChart.lift 𝔓 χ) := by
  haveI := 𝔓.eeta_iso
  set P := 𝔓.Meta.pointEquivPlace.symm w with hP
  have hwP : w = 𝔓.Meta.pointEquivPlace P := by rw [hP, Equiv.apply_symm_apply]
  suffices hfac : ∃ z : Spec (CommRingCat.of 𝕂) ⟶ TwoChartIntegralModel.XFin (R p) _ (jAt (ΓM M H) hj),
      P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = z ≫ ιFin p (ΓM M H) hj by
    obtain ⟨z, hz⟩ := hfac
    obtain ⟨χ', hχ'⟩ := exists_eq_lift_of_comp_eq 𝔓 P z hz
    have hw' : w = 𝔓.Meta.pointEquivPlace (WChart.lift 𝔓 χ') := by rw [hwP, hχ']
    have hχ : χ' = χ := by
      refine AlgHom.ext fun a => ?_
      exact Place.HasValue.unique (hread χ' a) (hw' ▸ hw a)
    rw [hw', hχ]
  set Qm := P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ with hQm
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) _ (jAt (ΓM M H) hj)
    (Qm.base (IsLocalRing.closedPoint 𝕂)) with hfin | hinf
  ·
    have hsub : Set.range Qm.base ⊆ Set.range (ιFin p (ΓM M H) hj).base := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint 𝕂)]
      exact hfin
    exact ⟨IsOpenImmersion.lift (ιFin p (ΓM M H) hj) Qm hsub, (IsOpenImmersion.lift_fac _ _ _).symm⟩
  ·
    have hsub : Set.range Qm.base ⊆ Set.range (ιInf p (ΓM M H) hj).base := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint 𝕂)]
      exact hinf
    set z' := IsOpenImmersion.lift (ιInf p (ΓM M H) hj) Qm hsub with hz'
    have hz'fac : z' ≫ ιInf p (ΓM M H) hj = Qm := IsOpenImmersion.lift_fac _ _ _
    set r' : ↥(chartAlgInf p (ΓM M H) hj) →+* 𝕂 := (Spec.preimage z').hom with hr'
    have hz'r : z' = Spec.map (CommRingCat.ofHom r') := by
      rw [hr', CommRingCat.ofHom_hom, Spec.map_preimage]

    have hval := hreadInf P r' (by rw [← hQm, ← hz'fac, hz'r])
    have hval' := hw (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
    have hprod := Place.HasValue.mul hval (hwP ▸ hval')
    rw [bhat_jInvChartInf_mul_ahat_jChartFin] at hprod
    have h1 : (𝔓.Meta.pointEquivPlace P).HasValue 1 (1 : 𝕂) := by
      simpa using Place.hasValue_algebraMap (𝔓.Meta.pointEquivPlace P) (1 : 𝕂)
    have hunit : IsUnit (r' (TwoChartIntegralModel.jInvChartInf _ _ _)) :=
      IsUnit.of_mul_eq_one _ (Place.HasValue.unique hprod h1)

    letI := (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).toRingHom.toAlgebra
    haveI := TwoChartIntegralModel.isLocalization_away_inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    set r'' := IsLocalization.Away.lift (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
      (S := ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) hunit with hr''
    have hr''comp : r''.comp (TwoChartIntegralModel.inclInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).toRingHom = r' :=
      IsLocalization.Away.lift_comp _ hunit
    refine ⟨Spec.map (CommRingCat.ofHom r'') ≫ TwoChartIntegralModel.fFin (R p) _ (jAt (ΓM M H) hj), ?_⟩
    rw [Category.assoc, TwoChartIntegralModel.glue_condition, ← Category.assoc,
      TwoChartIntegralModel.fInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr''comp, ← hz'r, hz'fac]

theorem hasValue_smul {L F : Type*} [Field L] [Field F] [Algebra L F] (g : SemilinearAut L F) (v : Place L F)
    {x : F} {a : L} (h : v.HasValue x a) : (g • v).HasValue (g • x) (SemilinearAut.baseAut g a) := by
  obtain ⟨hx, hres⟩ := h
  have hmem : g • x ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g x v.toValuationSubring hx
  refine ⟨hmem, ?_⟩
  have key : IsLocalRing.residue (g • v).toValuationSubring
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩) =
      SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  have hx' : (⟨g • x, hmem⟩ : (g • v).toValuationSubring) =
      SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩ := rfl
  rw [hx', key, hres, SemilinearAut.smulResidueRingEquiv_algebraMap]

theorem hasValue_ofAlgAut_smul {L F : Type*} [Field L] [Field F] [Algebra L F] (φ : F ≃ₐ[L] F) (v : Place L F)
    {x : F} {a : L} (h : v.HasValue x a) : (SemilinearAut.ofAlgAut φ • v).HasValue (φ x) a := by
  have := hasValue_smul (SemilinearAut.ofAlgAut φ) v h
  rwa [SemilinearAut.ofAlgAut_smul, SemilinearAut.baseAut_ofAlgAut] at this

theorem pointEquivPlace_lift_precomp
    (hread : ∀ (χ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂) (a : ↥(chartAlgFin p (ΓM M H) hj)),
      (𝔓.Meta.pointEquivPlace (WChart.lift 𝔓 χ)).HasValue (ahat a) (χ a))
    (hreadInf : ∀ (Q : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
      (r' : ↥(chartAlgInf p (ΓM M H) hj) →+* 𝕂),
      Q.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom r') ≫ ιInf p (ΓM M H) hj →
        (𝔓.Meta.pointEquivPlace Q).HasValue (bhat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) (r' (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))))
    (φ : ↥(xHFunctionFieldBar M H) ≃ₐ[𝕂] ↥(xHFunctionFieldBar M H))
    (τ : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hτ : ∀ a : ↥(chartAlgFin p (ΓM M H) hj), ahat (p := p) (M := M) (H := H) (hj := hj) (τ a) = φ.symm (ahat a))
    (ρ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] 𝕂) :
    𝔓.Meta.pointEquivPlace (WChart.lift 𝔓 (WChart.precomp ρ τ)) =
      SemilinearAut.ofAlgAut φ • 𝔓.Meta.pointEquivPlace (WChart.lift 𝔓 ρ) := by
  symm
  refine place_eq_pointEquivPlace_lift_of_forall_hasValue 𝔓 hread hreadInf (WChart.precomp ρ τ) _ fun a => ?_
  have h1 := hread ρ (τ a)
  have h2 := hasValue_ofAlgAut_smul φ _ h1
  rw [hτ, AlgEquiv.apply_symm_apply] at h2
  exact h2

end WChart
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart"

universe u

namespace FinRead

section Value

variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}

theorem stalkClosedPointTo_germ_appIso_inv (ι : Y ⟶ X) [IsOpenImmersion ι] (l : Spec R ⟶ Y)
    (w : Γ(Y, ⊤)) (h : (l ≫ ι).base (IsLocalRing.closedPoint R) ∈ ι ''ᵁ ⊤) :
    Scheme.stalkClosedPointTo (l ≫ ι) (X.presheaf.germ (ι ''ᵁ ⊤) _ h ((ι.appIso ⊤).inv w)) =
      Scheme.stalkClosedPointTo l (Y.presheaf.germ ⊤ _ trivial w) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show Scheme.stalkClosedPointTo l (ι.stalkMap (l.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base (l.base (IsLocalRing.closedPoint R))) h ((ι.appIso ⊤).inv w))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]

theorem stalkClosedPointTo_SpecMap_germ {A : CommRingCat.{u}} (φ : A ⟶ R) (b : A) :
    Scheme.stalkClosedPointTo (Spec.map φ) ((Spec A).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso A).inv b)) =
      φ b := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

theorem stalkClosedPointTo_congr {g g' : Spec R ⟶ X} (hg : g = g') (U : X.Opens)
    (h : g.base (IsLocalRing.closedPoint R) ∈ U) (h' : g'.base (IsLocalRing.closedPoint R) ∈ U) (s : Γ(X, U)) :
    Scheme.stalkClosedPointTo g (X.presheaf.germ U _ h s) = Scheme.stalkClosedPointTo g' (X.presheaf.germ U _ h' s) := by
  subst hg; rfl

theorem stalkClosedPointTo_germ_app (y : Spec R ⟶ Y) (f : Y ⟶ X) (U : X.Opens)
    (h : (y ≫ f).base (IsLocalRing.closedPoint R) ∈ U) :
    ∀ s : Γ(X, U), Scheme.stalkClosedPointTo y (Y.presheaf.germ (f ⁻¹ᵁ U) (y.base (IsLocalRing.closedPoint R)) h (f.app U s)) =
      Scheme.stalkClosedPointTo (y ≫ f) (X.presheaf.germ U _ h s) := by
  intro s
  rw [Scheme.stalkClosedPointTo_comp]
  show _ = Scheme.stalkClosedPointTo y (f.stalkMap (y.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ U (f.base (y.base (IsLocalRing.closedPoint R))) h s))
  rw [Scheme.Hom.germ_stalkMap_apply]

end Value
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart"

theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    (s : Γ(X, U)) :
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = X.germToFunctionField U s := by
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  show (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (X.presheaf.germ U x hx s) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

end FinRead
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart"

namespace ModularCurve p2m_export "ModularCurve" "XHDRModelAtP infSubgroup xHFunctionFieldBar qExpFunctionFieldC qExpand coeffEmb coeffEmb_mem_laurentBaseChange jqModC XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb XHDRLevel.exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic" namespace XHDRModelAtP p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta_chart_nonempty w Meta dia_generic normal hgal lfp Meta_pin heeta isProper eeta_iso flat w_over comp w_sq coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb" end ModularCurve.XHDRModelAtP
p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open FinRead in

theorem ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf_of_pin
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    [hne : Nonempty (Scheme.Opens.toScheme ((𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))]
    (hpin : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ((𝔓.Meta.ffEquiv.symm
          (𝔓.Meta.C.germToFunctionField
            ((𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
                ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b))))
          : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))
    (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
    (χ : ↥(chartAlgInf p (ΓM M H) hj) →+* AlgebraicClosure ℚ)
    (hQ : Q.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
      Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj)
    (b : ↥(chartAlgInf p (ΓM M H) hj)) :
    (𝔓.Meta.pointEquivPlace Q).HasValue
      ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ (χ b) := by

  set f := 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hf
  set U : (X p (ΓM M H) hj).Opens := (ιInf p (ΓM M H) hj) ''ᵁ ⊤ with hU
  set sec : Γ(X p (ΓM M H) hj, U) :=
    ((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b)
    with hsec
  have hQf : Q.1 ≫ f = Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj := by rw [hf]; exact hQ
  have hmemU : (Q.1 ≫ f).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := by
    rw [hQf]
    exact ⟨(Spec.map (CommRingCat.ofHom χ)).base (IsLocalRing.closedPoint _), trivial, rfl⟩
  have hmemU' : (Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj).base
      (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := hQf ▸ hmemU
  set s := 𝔓.Meta.C.presheaf.germ (f ⁻¹ᵁ U) (Q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hmemU
    (f.app U sec) with hs
  obtain ⟨hmem, hres, -⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo 𝔓.Meta Q s
  have helt : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ := by
    apply Subtype.ext
    rw [hs, algebraMap_germ_eq_germToFunctionField]
    exact hpin b
  have hval : (Scheme.stalkClosedPointTo Q.1).hom s = χ b := by
    show Scheme.stalkClosedPointTo Q.1 s = χ b
    rw [hs, stalkClosedPointTo_germ_app Q.1 f U hmemU sec, stalkClosedPointTo_congr hQf U hmemU hmemU' sec, hsec,
      stalkClosedPointTo_germ_appIso_inv, stalkClosedPointTo_SpecMap_germ]
    rfl
  have H' : ∃ h : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) ∈
      (𝔓.Meta.pointEquivPlace Q).toValuationSubring,
      IsLocalRing.residue (𝔓.Meta.pointEquivPlace Q).toValuationSubring ⟨_, h⟩ =
        algebraMap (AlgebraicClosure ℚ) (𝔓.Meta.pointEquivPlace Q).ResidueField (χ b) :=
    ⟨hmem, by rw [hres, hval]⟩
  rw [helt] at H'
  exact H'

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in

theorem ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
    (χ : ↥(chartAlgInf p (ΓM M H) hj) →+* AlgebraicClosure ℚ)
    (hQ : Q.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
      Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj)
    (b : ↥(chartAlgInf p (ΓM M H) hj)) :
    (𝔓.Meta.pointEquivPlace Q).HasValue
      ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ (χ b) := by
  obtain ⟨hne, _⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
    p M H hpM hj 𝔓 b
  haveI := hne
  refine ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf_of_pin 𝔓 (fun b' => ?_) Q χ hQ b
  obtain ⟨_, h⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
    p M H hpM hj 𝔓 b'
  exact h

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open FinRead in

theorem ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιFin
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
    (r' : ↥(chartAlgFin p (ΓM M H) hj) →+* AlgebraicClosure ℚ)
    (hQ : Q.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
      Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj)
    (a : ↥(chartAlgFin p (ΓM M H) hj)) :
    (𝔓.Meta.pointEquivPlace Q).HasValue
      ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ (r' a) := by
  haveI := 𝔓.Meta_chart_nonempty

  set f := 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hf
  set U : (X p (ΓM M H) hj).Opens := (ιFin p (ΓM M H) hj) ''ᵁ ⊤ with hU
  set sec : Γ(X p (ΓM M H) hj, U) :=
    ((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a)
    with hsec

  have hQf : Q.1 ≫ f = Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj := by rw [hf]; exact hQ
  have hmemU : (Q.1 ≫ f).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := by
    rw [hQf]
    exact ⟨(Spec.map (CommRingCat.ofHom r')).base (IsLocalRing.closedPoint _), trivial, rfl⟩
  have hmemU' : (Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj).base
      (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := hQf ▸ hmemU

  set s := 𝔓.Meta.C.presheaf.germ (f ⁻¹ᵁ U) (Q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hmemU
    (f.app U sec) with hs
  obtain ⟨hmem, hres, -⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo 𝔓.Meta Q s

  have helt : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ := by
    apply Subtype.ext
    rw [hs, algebraMap_germ_eq_germToFunctionField]
    exact 𝔓.Meta_pin a

  have hval : (Scheme.stalkClosedPointTo Q.1).hom s = r' a := by
    show Scheme.stalkClosedPointTo Q.1 s = r' a
    rw [hs, stalkClosedPointTo_germ_app Q.1 f U hmemU sec, stalkClosedPointTo_congr hQf U hmemU hmemU' sec, hsec,
      stalkClosedPointTo_germ_appIso_inv, stalkClosedPointTo_SpecMap_germ]
    rfl
  have H' : ∃ h : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) ∈
      (𝔓.Meta.pointEquivPlace Q).toValuationSubring,
      IsLocalRing.residue (𝔓.Meta.pointEquivPlace Q).toValuationSubring ⟨_, h⟩ =
        algebraMap (AlgebraicClosure ℚ) (𝔓.Meta.pointEquivPlace Q).ResidueField (r' a) :=
    ⟨hmem, by rw [hres, hval]⟩
  rw [helt] at H'
  exact H'

namespace WChart

open FinRead

theorem main
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj),
      ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj ∧
      𝔛.w.hom ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (ΓM M H) hj).opensRange ∧
      (∀ (b : ↥(chartAlgFin p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by
  haveI := 𝔛.isProper
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI := 𝔛.flat
  haveI := 𝔛.lfp
  haveI := 𝔛.eeta_iso

  obtain ⟨σ, theta, -, -, hread⟩ :=
    ModularCurve.XHDRLevel.exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic p M H hpM hpM2 hHp hj θ hθ

  have hf : ιFin p (ΓM M H) hj ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj))) :=
    TwoChartIntegralModel.ιFin_toBase _ _ _
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)))) := by
    rw [← hf]; infer_instance
  haveI : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)))) := by
    rw [← hf]; infer_instance
  have h1 : ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj := by
    refine AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
      (R := R p) ℚ (AlgebraicClosure ℚ)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj))))
      (toBase p (ΓM M H) hj) _ _ ?_ ?_ ?_
    · rw [Category.assoc, 𝔛.w_over, hf]
    · rw [Category.assoc, hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => theta.commutes r
    · intro x hx

      have hreadFin : ∀ (χ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] AlgebraicClosure ℚ) (a : ↥(chartAlgFin p (ΓM M H) hj)),
          (𝔛.Meta.pointEquivPlace (WChart.lift 𝔛 χ)).HasValue (WChart.ahat a) (χ a) := fun χ a =>
        ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιFin 𝔛 (WChart.lift 𝔛 χ) χ.toRingHom
          (by rw [← Category.assoc, WChart.lift_eeta, WChart.liftBar_fst]) a
      have hreadInf : ∀ (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // s ≫ 𝔛.Meta.toBase = 𝟙 _})
          (r' : ↥(chartAlgInf p (ΓM M H) hj) →+* AlgebraicClosure ℚ),
          Q.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom r') ≫ ιInf p (ΓM M H) hj →
          (𝔛.Meta.pointEquivPlace Q).HasValue
            (WChart.bhat (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)))
            (r' (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) :=
        fun Q r' h => ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf 𝔛 Q r' h _

      have hτ : ∀ a : ↥(chartAlgFin p (ΓM M H) hj),
          WChart.ahat (p := p) (M := M) (H := H) (hj := hj) (theta.symm a) = θ.symm (WChart.ahat a) := by
        intro a
        have h := hread (theta.symm a) (WChart.ahat (theta.symm a)) rfl
        rw [AlgEquiv.apply_symm_apply] at h
        have h' : θ (WChart.ahat (theta.symm a)) = WChart.ahat a := Subtype.ext h
        rw [eq_comm, AlgEquiv.symm_apply_eq]
        exact h'.symm
      have hRHS : ∀ ρ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] AlgebraicClosure ℚ,
          𝔛.Meta.pointEquivPlace (WChart.lift 𝔛 (WChart.precomp ρ theta.symm)) =
            SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace (WChart.lift 𝔛 ρ) :=
        fun ρ => WChart.pointEquivPlace_lift_precomp 𝔛 hreadFin hreadInf θ theta.symm hτ ρ

      obtain ⟨ρ, hxρ⟩ : ∃ ρ : ↥(chartAlgFin p (ΓM M H) hj) →ₐ[R p] AlgebraicClosure ℚ,
          x = Spec.map (CommRingCat.ofHom ρ.toRingHom) := by
        have hxf : Spec.map (Spec.preimage x) = x := Spec.map_preimage x
        have hcomm : (Spec.preimage x).hom.comp (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)) =
            algebraMap (R p) (AlgebraicClosure ℚ) := by
          have h1 : Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj)) ≫ Spec.preimage x) =
              Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
            rw [Spec.map_comp, hxf]; exact hx
          exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
        refine ⟨{ (Spec.preimage x).hom with commutes' := fun r => ?_ }, ?_⟩
        · exact congrArg (fun g => g r) hcomm
        · calc x = Spec.map (Spec.preimage x) := hxf.symm
            _ = _ := rfl
      subst hxρ

      have hA := WChart.pointEquivPlace_eq_smul_translate 𝔛 θ hwgen (WChart.lift 𝔛 ρ)
      have hB := hRHS (WChart.precomp ρ theta)
      have hpp : WChart.precomp (WChart.precomp ρ theta) theta.symm = ρ := by
        refine AlgHom.ext fun a => ?_
        show ρ (theta (theta.symm a)) = ρ a
        rw [AlgEquiv.apply_symm_apply]
      rw [hpp] at hB
      have hpl : 𝔛.Meta.pointEquivPlace (WChart.translate 𝔛 (WChart.lift 𝔛 ρ)) =
          𝔛.Meta.pointEquivPlace (WChart.lift 𝔛 (WChart.precomp ρ theta)) :=
        (smul_left_cancel_iff _).mp (hA.symm.trans hB)
      have hsec : WChart.translate 𝔛 (WChart.lift 𝔛 ρ) = WChart.lift 𝔛 (WChart.precomp ρ theta) :=
        𝔛.Meta.pointEquivPlace.injective hpl
      have hbar : WChart.liftBar (WChart.precomp ρ theta) = WChart.liftBar ρ ≫ WChart.wBar 𝔛 := by
        rw [← WChart.lift_eeta 𝔛, ← hsec, WChart.translate_lift_eeta]
      have hfst := congrArg (fun g => g ≫ pullback.fst _ _) hbar
      simp only [Category.assoc, WChart.liftBar_fst, WChart.wBar_fst, WChart.liftBar_fst_assoc] at hfst
      have hsplit : Spec.map (CommRingCat.ofHom (WChart.precomp ρ theta).toRingHom) =
          Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
      rw [← hfst, hsplit, Category.assoc]

  have h1inv : ιFin p (ΓM M H) hj ≫ 𝔛.w.inv =
      Spec.map (CommRingCat.ofHom theta.symm.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj := by
    have h := congrArg (fun g => Spec.map (CommRingCat.ofHom theta.symm.toRingEquiv.toRingHom) ≫ g ≫ 𝔛.w.inv) h1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    rw [← Category.assoc (Spec.map _) (Spec.map _), ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    have hid : theta.symm.toRingEquiv.toRingHom.comp theta.toRingEquiv.toRingHom =
        RingHom.id ↥(chartAlgFin p (ΓM M H) hj) := RingHom.ext fun a => theta.symm_apply_apply a
    rw [hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h
    exact h.symm
  refine ⟨theta, h1, ?_, hread⟩

  ext x
  constructor
  · rintro ⟨y, hy⟩

    have hx : x = 𝔛.w.inv.base (𝔛.w.hom.base x) := by
      show x = (𝔛.w.hom ≫ 𝔛.w.inv).base x
      rw [Iso.hom_inv_id]
      rfl
    refine ⟨(Spec.map (CommRingCat.ofHom theta.symm.toRingEquiv.toRingHom)).base y, ?_⟩
    show (Spec.map (CommRingCat.ofHom theta.symm.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj).base y = x
    rw [← h1inv]
    show 𝔛.w.inv.base ((ιFin p (ΓM M H) hj).base y) = x
    rw [hy, ← hx]
  · rintro ⟨y, hy⟩
    refine ⟨(Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom)).base y, ?_⟩
    show ((Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom)) ≫ ιFin p (ΓM M H) hj).base y = 𝔛.w.hom.base x
    rw [← h1]
    show 𝔛.w.hom.base ((ιFin p (ΓM M H) hj).base y) = 𝔛.w.hom.base x
    rw [hy]

end WChart
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart"

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj),

      ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj ∧
      𝔛.w.hom ⁻¹ᵁ (ιFin p (ΓM M H) hj).opensRange = (ιFin p (ΓM M H) hj).opensRange ∧

      (∀ (b : ↥(chartAlgFin p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by
  exact WChart.main p M H hpM hpM2 hHp hj 𝔛 θ hθ hwgen

end S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap (solution)
