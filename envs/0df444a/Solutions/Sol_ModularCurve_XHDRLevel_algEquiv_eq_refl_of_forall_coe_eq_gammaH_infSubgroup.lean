-- Prove2me | solution 1 for ModularCurve.XHDRLevel.algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8e81224a-a7f4-500e-8ea3-20c373804d9e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_algEquiv_eq_refl_of_forall_coe_eq_infSubgroup
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffEmb_injective ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

namespace RigH

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
  | succ n ih =>
    rw [zpow_add_one, AlgEquiv.mul_apply, hx]; exact ih
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

end RigH

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (τ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hτ : ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) → τ f = f) :
    τ = AlgEquiv.refl := by
  classical

  obtain ⟨τbar, hτbar⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) (xHFunctionField M H)
    (τ.toRingEquiv : ↥(xHFunctionField M H) ≃+* ↥(xHFunctionField M H))

  have hfixN : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((τbar f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f u hfu

    let Fix : IntermediateField (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := IntermediateField.fixedField (Subgroup.zpowers τbar)
    have hle : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ IntermediateField.lift Fix := by

      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxM : x ∈ (xHFunctionField M H : IntermediateField ℚ (LaurentSeries ℚ)) :=
        qExpFunctionFieldC_mono ℚ (RigH.gammaH_le_gammaH_div p M H hpM) hx
      let xM : ↥(qExpFunctionFieldC ℚ (ΓM M H)) := ⟨x, hxM⟩
      have hfixx : τ xM = xM := hτ xM ⟨x, hx⟩ rfl
      let e : ↥(xHFunctionFieldBar M H) := ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hxM⟩
      have he : τbar e = e := by
        apply Subtype.ext
        have this2 : ((τbar e : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (((τ xM : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := hτbar xM
        rw [hfixx] at this2
        exact this2
      show ((e : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.lift Fix
      exact (IntermediateField.mem_lift e).mpr (RigH.mem_fixedField_zpowers τbar he)
    have hfmem : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.lift Fix := by
      rw [hfu]; exact hle u.2
    have hfFix : f ∈ Fix := (IntermediateField.mem_lift f).mp hfmem
    have : τbar f = f := (IntermediateField.mem_fixedField_iff _ _).mp hfFix τbar (Subgroup.mem_zpowers τbar)
    rw [this]; exact hfu
  have key := ModularCurve.algEquiv_eq_refl_of_forall_coe_eq_infSubgroup p M H hpM hpM2 hHp τbar hfixN

  apply AlgEquiv.ext
  intro f
  have h : ((τbar ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
      ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((τ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := hτbar f
  rw [key, AlgEquiv.coe_refl, id] at h

  apply Subtype.ext
  exact (RigH.coeffEmb_injective (AlgebraicClosure ℚ) h).symm

end S_ModularCurve_XHDRLevel_algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup (solution)
