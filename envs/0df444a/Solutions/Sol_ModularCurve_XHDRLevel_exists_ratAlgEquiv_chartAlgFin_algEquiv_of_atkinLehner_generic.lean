-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/543b819e-9077-5c1d-a830-8b39f206ffad

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_algEquiv_eq_refl_of_forall_coe_eq_infSubgroup
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffEmb_qExpand~coeffEmb_injective ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace WChartField

theorem mem_fixedField_zpowers {F E : Type*} [Field F] [Field E] [Algebra F E] (g : E ≃ₐ[F] E) {x : E} (hx : g x = x) :
    x ∈ IntermediateField.fixedField (Subgroup.zpowers g) := by
  rw [IntermediateField.mem_fixedField_iff]
  rintro h ⟨n, rfl⟩
  have hsymm : g.symm x = x := by
    conv_lhs => rw [← hx]
    exact g.symm_apply_apply x
  show (g ^ n) x = x
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hx]; exact ih
  | pred n ih =>
    rw [zpow_sub_one, AlgEquiv.mul_apply]
    have : (g⁻¹ : E ≃ₐ[F] E) x = x := hsymm
    rw [this]; exact ih

theorem coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (coeffEmb L) := by
  intro x y h
  ext k
  have := congrArg (fun s : LaurentSeries L => s.coeff k) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ L).injective this

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N x hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ N x) = qExpand L N (coeffEmb L x) :=
  coeffMap_qExpand (algebraMap ℚ L) N x

theorem gammaH_le_gammaH_div (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by
  intro A hA
  obtain ⟨hA0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hdvd : M / p ∣ M := Nat.div_dvd_of_dvd hpM
  have hA0' : A ∈ CongruenceSubgroup.Gamma0 (M / p) := by
    rw [CongruenceSubgroup.Gamma0_mem] at hA0 ⊢
    have := congrArg (ZMod.castHom hdvd (ZMod (M / p))) hA0
    rwa [map_intCast, map_zero] at this
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0', ?_⟩
  have hunits : CohCarrier.gamma0Units (M / p) ⟨A, hA0'⟩ = ZMod.unitsMap hdvd (CohCarrier.gamma0Units M ⟨A, hA0⟩) := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units]
    show (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (M / p)) = ZMod.castHom hdvd (ZMod (M / p)) (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)
    rw [map_intCast]
  rw [hunits]
  exact unitsMap_mem_infSubgroup p M H hpM hH

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)

include hpM2 hHp in

theorem theta_coeffEmb
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
        ((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ)) :
    ∀ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
      ((θ ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
        ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨σbar, hσbar⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) (xHFunctionField M H)
    (σ.toRingEquiv : ↥(xHFunctionField M H) ≃+* ↥(xHFunctionField M H))

  let τ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H) := σbar.trans θ.symm
  have hτ : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((τ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f u hfu
    let Fix : IntermediateField (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := IntermediateField.fixedField (Subgroup.zpowers τ)
    have hle : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ IntermediateField.lift Fix := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxM : x ∈ (xHFunctionField M H : IntermediateField ℚ (LaurentSeries ℚ)) :=
        qExpFunctionFieldC_mono ℚ (gammaH_le_gammaH_div p M H hpM) hx
      let xM : ↥(qExpFunctionFieldC ℚ (ΓM M H)) := ⟨x, hxM⟩
      let e : ↥(xHFunctionFieldBar M H) := ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hxM⟩
      let eN : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
        ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩

      have h1 : ((σbar e : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) x) := by
        have this2 : ((σbar e : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (((σ xM : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := hσbar xM
        rw [hσ xM ⟨x, hx⟩ rfl, coeffEmb_qExpand] at this2
        exact this2
      have h2 : ((θ e : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) x) :=
        hθ e eN rfl
      have he : τ e = e := by
        show θ.symm (σbar e) = e
        rw [AlgEquiv.symm_apply_eq]
        exact Subtype.ext (h1.trans h2.symm)
      show ((e : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.lift Fix
      exact (IntermediateField.mem_lift e).mpr (mem_fixedField_zpowers τ he)
    have hfmem : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.lift Fix := by
      rw [hfu]; exact hle u.2
    have hfFix : f ∈ Fix := (IntermediateField.mem_lift f).mp hfmem
    have : τ f = f := (IntermediateField.mem_fixedField_iff _ _).mp hfFix τ (Subgroup.mem_zpowers τ)
    rw [this]; exact hfu
  have key := ModularCurve.algEquiv_eq_refl_of_forall_coe_eq_infSubgroup p M H hpM hpM2 hHp τ hτ
  intro f
  have h : τ ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ =
      ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ := by rw [key]; rfl
  change θ.symm (σbar _) = _ at h
  rw [AlgEquiv.symm_apply_eq] at h
  rw [← h]
  exact hσbar f

end WChartField

namespace WChartField

p2m_open "ModularCurve~coeffEmb_qExpand~coeffEmb_injective ModularCurve.XHDRLevel Polynomial AlgebraicGeometry.Polynomial"

theorem mem_chartAlgFin_of_coe_eq_qExpand_jqModC (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (y : ↥(qExpFunctionFieldC ℚ Γ))
    (hy : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; (y : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ)) :
    y ∈ chartAlgFin p Γ hj := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  let F : Type := ↥(qExpFunctionFieldC ℚ Γ)
  let A : Subalgebra (R p) F := Algebra.adjoin (R p) ({jAt Γ hj} : Set F)
  let jA : ↥A := ⟨jAt Γ hj, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let P : Polynomial ↥A := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥A) jA)
  have hPmonic : P.Monic := data.monic.map _
  show IsIntegral (↥A) y
  refine ⟨P, hPmonic, ?_⟩
  let c : F →+* LaurentSeries ℚ := (qExpFunctionFieldC ℚ Γ).toSubfield.subtype
  have hc : ∀ z : F, c z = (z : LaurentSeries ℚ) := fun _ => rfl
  have hcinj : Function.Injective c := Subtype.coe_injective
  apply hcinj
  rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂, hc y, hy]
  have step : c.comp ((algebraMap (↥A) F).comp (Polynomial.eval₂RingHom (Int.castRingHom ↥A) jA)) = evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X, hc]
    show ((jAt Γ hj : F) : LaurentSeries ℚ) = jq
    rw [coe_jAt, jqModC_rat]
  rw [step]
  have e : qExpand ℚ p (jqModC ℚ) = jqN p := by rw [jqModC_rat]; rfl
  rw [e]
  exact data.eval_eq_zero

theorem exists_algEquiv_chartAlgFin_coe_eq (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ))
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σ : ↥(qExpFunctionFieldC ℚ Γ) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ Γ))
    (h1 : σ (jAt Γ hj) ∈ chartAlgFin p Γ hj) (h2 : σ.symm (jAt Γ hj) ∈ chartAlgFin p Γ hj) :
    ∃ theta : ↥(chartAlgFin p Γ hj) ≃ₐ[R p] ↥(chartAlgFin p Γ hj),
      ∀ b : ↥(chartAlgFin p Γ hj), ((theta b : ↥(chartAlgFin p Γ hj)) : ↥(qExpFunctionFieldC ℚ Γ)) = σ (b : ↥(qExpFunctionFieldC ℚ Γ)) := by
  classical
  let F : Type := ↥(qExpFunctionFieldC ℚ Γ)
  let O : Subalgebra (R p) F := chartAlgFin p Γ hj
  let A : Subalgebra (R p) F := Algebra.adjoin (R p) ({jAt Γ hj} : Set F)

  have hfixR : ∀ (τ : F ≃ₐ[ℚ] F) (r : R p), τ (algebraMap (R p) F r) = algebraMap (R p) F r := by
    intro τ r
    have hext : ∀ (f g : R p →+* F), f = g := by
      intro f g
      haveI : IsLocalization.AtPrime (R p) (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
      exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)
    have e : algebraMap (R p) F = (algebraMap ℚ F).comp (algebraMap (R p) ℚ) := hext _ _
    rw [e, RingHom.comp_apply, AlgEquiv.commutes]

  have hstab : ∀ (τ : F ≃ₐ[ℚ] F), τ (jAt Γ hj) ∈ O → ∀ x ∈ O, τ x ∈ O := by
    intro τ hτj x hx
    have hA : ∀ a ∈ A, τ a ∈ O := by
      intro a ha
      refine Algebra.adjoin_induction (hx := ha) ?_ ?_ ?_ ?_
      · rintro _ rfl; exact hτj
      · intro r; rw [hfixR]; exact Subalgebra.algebraMap_mem _ r
      · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
      · intro a b _ _ ha hb; rw [map_mul]; exact mul_mem ha hb
    have hxint : IsIntegral (↥A) x := hx

    let IC : Subalgebra (↥A) F := integralClosure (↥A) F
    have hICO : ∀ z : F, z ∈ IC ↔ z ∈ O := fun z => Iff.rfl
    let φ : ↥A →+* ↥IC := ((τ : F →+* F).comp A.val.toRingHom).codRestrict IC.toSubring (fun a => (hICO _).mpr (hA a a.2))
    have hcomp : (algebraMap (↥IC) F).comp φ = (τ : F →+* F).comp (algebraMap (↥A) F) := by
      ext a; rfl
    have hint : IsIntegral (↥IC) (τ x) := IsIntegral.map_of_comp_eq φ (τ : F →+* F) hcomp hxint
    exact (hICO _).mp (isIntegral_trans (R := ↥A) (τ x) hint)
  have hσO : ∀ x ∈ O, σ x ∈ O := hstab σ h1
  have hσ'O : ∀ x ∈ O, σ.symm x ∈ O := hstab σ.symm h2

  let t : ↥O →ₐ[R p] ↥O :=
    { toFun := fun b => ⟨σ b, hσO b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun r => Subtype.ext (by
        show σ (algebraMap (R p) F r) = algebraMap (R p) F r
        exact hfixR σ r) }
  let t' : ↥O →ₐ[R p] ↥O :=
    { toFun := fun b => ⟨σ.symm b, hσ'O b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun r => Subtype.ext (by
        show σ.symm (algebraMap (R p) F r) = algebraMap (R p) F r
        exact hfixR σ.symm r) }
  refine ⟨AlgEquiv.ofAlgHom t t' (AlgHom.ext fun b => Subtype.ext (σ.apply_symm_apply _)) (AlgHom.ext fun b => Subtype.ext (σ.symm_apply_apply _)), fun b => rfl⟩

end WChartField

p2m_open "ModularCurve~coeffEmb_qExpand~coeffEmb_injective" in open  ModularCurve.XHDRLevel in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
      (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)),

      (∀ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
        ((θ ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
          ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))) ∧

      (∀ b : ↥(chartAlgFin p (ΓM M H) hj),
        ((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = σ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) ∧

      (∀ (b : ↥(chartAlgFin p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out

  obtain ⟨σ, hσi, hσii⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  have ha := WChartField.theta_coeffEmb p M H hpM hpM2 hHp θ hθ σ hσi

  let jF : ↥(qExpFunctionFieldC ℚ (ΓM M H)) := jAt (ΓM M H) hj
  let j0 : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) := jAt (ΓN p M H hpM) hj
  have hjF : ((jF : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ _
  have hj0 : ((j0 : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = jqModC ℚ := coe_jAt _ _
  have hσj : ((σ jF : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) := by
    rw [hσi jF j0 (by rw [hjF, hj0]), hj0]
  have h1 : σ jF ∈ chartAlgFin p (ΓM M H) hj := WChartField.mem_chartAlgFin_of_coe_eq_qExpand_jqModC p (ΓM M H) hj _ hσj
  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos).ne'⟩
  have hσσj : σ (σ jF) = jF := by
    have hcop : Nat.Coprime p (M / p) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
    have key := hσii (ZMod.unitOfCoprime p hcop) (ZMod.coe_unitOfCoprime p hcop) (σ jF) j0 (by rw [hσj, hj0])
    rw [ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (M / p) (infSubgroup p M H hpM) _ _
      (jqModC ℚ) (qExpFunctionFieldC_mono ℚ le_top hj) (by show coeffEmb _ _ = _; rw [hj0])] at key
    apply Subtype.ext
    apply WChartField.coeffEmb_injective (AlgebraicClosure ℚ)
    rw [key]
    show coeffEmb _ _ = _
    rw [hj0, hjF]
  have h2 : σ.symm jF ∈ chartAlgFin p (ΓM M H) hj := by
    have : σ.symm jF = σ jF := by rw [AlgEquiv.symm_apply_eq, hσσj]
    rw [this]; exact h1
  obtain ⟨theta, hb⟩ := WChartField.exists_algEquiv_chartAlgFin_coe_eq p (ΓM M H) hj σ h1 h2
  refine ⟨σ, theta, ha, hb, ?_⟩
  intro b f hf
  have hfe : f = ⟨coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ :=
    Subtype.ext hf
  rw [hfe, ha, ← hb b]

end S_ModularCurve_XHDRLevel_exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic (solution)
