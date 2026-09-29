-- Prove2me | solution 1 for ModularCurve.XHDRLevel.algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/65aa9db7-4100-5c5c-9eac-fe705e83d2e0

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic
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

p2m_open "ModularCurve~coeffEmb_qExpand~coeffEmb_injective" in open  ModularCurve.XHDRLevel in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
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
        coeffEmb (AlgebraicClosure ℚ) (((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) :=
  WChartField.theta_coeffEmb p M H hpM hpM2 hHp θ hθ σ hσ

end S_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic (solution)
