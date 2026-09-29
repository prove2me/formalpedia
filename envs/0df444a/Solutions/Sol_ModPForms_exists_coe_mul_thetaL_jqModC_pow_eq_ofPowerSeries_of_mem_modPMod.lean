-- Prove2me | solution 1 for ModPForms.exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bc0d7052-d89d-598e-a9f7-d79bbcea043a

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField
import Theorems.Thm_ModularCurve_coeffMap_mem_modularFunctionFieldC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.ProjectiveLine.map_mk ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open ModularCurve

noncomputable section

namespace BridgeMem

open HahnSeries

def thetaZ : LaurentSeries ℤ := single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ (jqModC ℤ)

theorem coeff_thetaZ (n : ℤ) : thetaZ.coeff n = n * (jqModC ℤ).coeff n := by
  rw [thetaZ, coeff_single_mul, one_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    show n - 1 + ((1 : ℕ) : ℤ) = n by push_cast; ring, Ring.choose_one_right, zsmul_eq_mul, Int.cast_id]

theorem coeff_thetaZ_neg_one : thetaZ.coeff (-1) = -1 := by
  rw [coeff_thetaZ, coeff_jqModC_neg_one]; ring

theorem coeff_thetaZ_of_lt {n : ℤ} (hn : n < -1) : thetaZ.coeff n = 0 := by
  rw [coeff_thetaZ, coeff_jqModC_of_lt ℤ hn, mul_zero]

theorem thetaZ_ne_zero : thetaZ ≠ 0 := fun h => by
  have := coeff_thetaZ_neg_one; rw [h] at this; simp at this

theorem order_thetaZ : thetaZ.order = -1 := by
  apply le_antisymm (order_le_of_coeff_ne_zero (by rw [coeff_thetaZ_neg_one]; norm_num))
  by_contra hlt
  exact HahnSeries.coeff_order_eq_zero.not.mpr thetaZ_ne_zero (coeff_thetaZ_of_lt (not_le.1 hlt))

theorem isUnit_thetaZ : IsUnit thetaZ := by
  rw [HahnSeries.isUnit_iff, leadingCoeff_eq, order_thetaZ, coeff_thetaZ_neg_one]
  exact isUnit_one.neg

theorem coeffMap_thetaZ {K : Type*} [Field K] (f : ℤ →+* K) : coeffMap f thetaZ = thetaL K (jqModC K) := by
  rw [thetaZ, ← thetaL_coeffMap_eq_coeffMap_single_mul_derivative, coeffMap_jqModC]

def yZ (a : ℕ → ℤ) (m : ℕ) : LaurentSeries ℤ :=
  ofPowerSeries ℤ ℤ (PowerSeries.mk a) * ((isUnit_thetaZ.unit⁻¹ ^ m : (LaurentSeries ℤ)ˣ) : LaurentSeries ℤ)

theorem map_mk {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ → R) :
    (PowerSeries.mk a).map f = PowerSeries.mk (fun n => f (a n)) := by
  ext n; simp [PowerSeries.coeff_map]

theorem coeffMap_yZ {K : Type*} [Field K] (f : ℤ →+* K) (a : ℕ → ℤ) (m : ℕ) :
    coeffMap f (yZ a m) = ofPowerSeries ℤ K (PowerSeries.mk fun n => (a n : K)) *
      (thetaL K (jqModC K))⁻¹ ^ m := by
  rw [yZ, map_mul, coeffMap_ofPowerSeries, map_mk, Units.val_pow_eq_pow_val, map_pow, map_units_inv,
    IsUnit.unit_spec, coeffMap_thetaZ]
  congr 1
  ext n; simp

theorem coeffMap_yZ_mul {K : Type*} [Field K] (f : ℤ →+* K) (a : ℕ → ℤ) (m : ℕ)
    (hT : thetaL K (jqModC K) ≠ 0) :
    coeffMap f (yZ a m) * thetaL K (jqModC K) ^ m = ofPowerSeries ℤ K (PowerSeries.mk fun n => (a n : K)) := by
  rw [coeffMap_yZ, mul_assoc, ← mul_pow, inv_mul_cancel₀ hT, one_pow, mul_one]

theorem coeffMap_yZ_mem_rat (N : ℕ) [NeZero N] (m : ℕ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)))
    (a : ℕ → ℤ) (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    coeffMap (Int.castRingHom ℚ) (yZ a m) ∈ modularFunctionFieldC ℚ N := by
  have h1 := ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField N m f a ha
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
  rw [coeffMap_yZ]
  exact h1

theorem mem_or_inv_mem_ratLocalizedAt (p : ℕ) (hp : p.Prime) (z : ℚ) :
    z ∈ GaloisRep.ratLocalizedAt p ∨ z⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
  by_cases h : z.den.Coprime p
  · exact Or.inl h
  · right
    show z⁻¹.den.Coprime p
    rw [Rat.den_inv]
    split_ifs with h0
    · exact Nat.coprime_one_left p
    · have hpd : p ∣ z.den := by
        by_contra hnd; exact h ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
      rw [Nat.Coprime, Nat.gcd_comm, ← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd hp]
      intro hpn
      have := Nat.dvd_gcd hpn hpd
      rw [z.reduced] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)

section Deg

variable (p : ℕ) [hp : Fact p.Prime] (F : Type*) [Field F] [CharP F p] (N : ℕ) [NeZero N]

def ringEquivOfMemIff {K K' L : Type*} [Field K] [Field K'] [Field L] [Algebra K L] [Algebra K' L]
    (A : IntermediateField K L) (B : IntermediateField K' L) (h : ∀ x : L, x ∈ A ↔ x ∈ B) : ↥A ≃+* ↥B where
  toFun x := ⟨x, (h x).1 x.2⟩
  invFun x := ⟨x, (h x).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem hdeg (hpN : ¬ p ∣ N) :
    Module.finrank (IntermediateField.adjoin F ({jqModC F} : Set (LaurentSeries F)))
      (IntermediateField.adjoin (IntermediateField.adjoin F ({jqModC F} : Set (LaurentSeries F)))
        ({jqNModC F N} : Set (LaurentSeries F))) = dedekindPsi N := by
  have hN : (N : F) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff F p N).1 h)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h8 := finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi F N hN
  have h69 := modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos F p N hpN
  rw [← h8]
  symm

  have hlift : IntermediateField.lift (IntermediateField.adjoin F
        ({⟨jqModC F, jqModC_mem_full F N⟩} : Set ↥(modularFunctionFieldFullC F N)))
      = IntermediateField.adjoin F ({jqModC F} : Set (LaurentSeries F)) := by
    rw [IntermediateField.lift_adjoin, Set.image_singleton]
  let e1 := IntermediateField.liftAlgEquiv (IntermediateField.adjoin F
        ({⟨jqModC F, jqModC_mem_full F N⟩} : Set ↥(modularFunctionFieldFullC F N)))
  let e2 := IntermediateField.equivOfEq hlift
  let i := (e1.trans e2).toRingEquiv

  have hcar : ∀ x : LaurentSeries F, x ∈ modularFunctionFieldFullC F N ↔
      x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin F ({jqModC F} : Set (LaurentSeries F))))
        ({jqNModC F N} : Set (LaurentSeries F)) := by
    intro x
    rw [← h69]
    have hres := IntermediateField.adjoin_simple_adjoin_simple F (jqModC F) (jqNModC F N)
    exact (SetLike.ext_iff.1 hres x).symm
  let jj := ringEquivOfMemIff _ _ hcar
  refine Algebra.finrank_eq_of_equiv_equiv i jj (RingHom.ext fun x => Subtype.ext ?_)
  simp only [i, jj, e1, e2, ringEquivOfMemIff, IntermediateField.algebraMap_apply, RingHom.coe_comp,
    Function.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, RingEquiv.coe_mk, Equiv.coe_fn_mk]
  first
  | exact IntermediateField.liftAlgEquiv_apply _ x
  | (have key : ∀ y : ↥(IntermediateField.lift (IntermediateField.adjoin F
          ({⟨jqModC F, jqModC_mem_full F N⟩} : Set ↥(modularFunctionFieldFullC F N)))),
          ((IntermediateField.equivOfEq hlift y : ↥(IntermediateField.adjoin F ({jqModC F} : Set (LaurentSeries F))))
            : LaurentSeries F) = (y : LaurentSeries F) := fun _ => rfl
     rw [key]
     exact IntermediateField.liftAlgEquiv_apply _ x)

end Deg

theorem C_eq_algebraMap' {F : Type*} [Field F] (a : F) :
    (HahnSeries.C a : LaurentSeries F) = algebraMap F (LaurentSeries F) a := by
  rw [HahnSeries.algebraMap_apply']
  simp

theorem thetaL_jqModC_ne_zero (F : Type*) [Field F] : thetaL F (jqModC F) ≠ 0 := by
  intro h
  have := congrArg (fun x : LaurentSeries F => x.coeff (-1)) h
  simp only [HahnSeries.coeff_zero] at this
  rw [← coeffMap_thetaZ (Int.castRingHom F), coeffMap_coeff, coeff_thetaZ_neg_one] at this
  simp at this

theorem main (p : ℕ) [hp : Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (F : Type) [Field F] [CharP F p] (m : ℕ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) F) :
    ∃ G : ↥(modularFunctionFieldC F N),
      (G : LaurentSeries F) * thetaL F (jqModC F) ^ m = HahnSeries.ofPowerSeries ℤ F φ := by
  have hT := thetaL_jqModC_ne_zero F

  let O := GaloisRep.ratLocalizedAt p
  haveI : IsDiscreteValuationRing ↥O := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out
  let res : ↥O →+* F := (ZMod.castHom (dvd_refl p) F).comp (GaloisRep.ratLocalizedAtResidue p)
  let ι : ℤ →+* ↥O := Int.castRingHom ↥O

  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, a, ha, rfl⟩ := hφ

    have hmemQ := coeffMap_yZ_mem_rat N m f a ha
    have hyO : coeffMap O.subtype (coeffMap ι (yZ a m)) = coeffMap (Int.castRingHom ℚ) (yZ a m) := by
      rw [coeffMap_coeffMap]; exact coeffMap_congr (RingHom.ext_int _ _) _
    have hmemF := coeffMap_mem_modularFunctionFieldC O (mem_or_inv_mem_ratLocalizedAt p hp.out) res N
      (hdeg p F N hpN) hmemQ (coeffMap ι (yZ a m)) hyO
    refine ⟨⟨coeffMap res (coeffMap ι (yZ a m)), hmemF⟩, ?_⟩
    show coeffMap res (coeffMap ι (yZ a m)) * thetaL F (jqModC F) ^ m = _
    rw [coeffMap_coeffMap, coeffMap_congr (RingHom.ext_int (res.comp ι) (Int.castRingHom F)),
      coeffMap_yZ_mul _ a m hT]
  | zero => exact ⟨0, by simp⟩
  | add φ ψ _ _ hφ hψ =>
    obtain ⟨G, hG⟩ := hφ
    obtain ⟨H, hH⟩ := hψ
    exact ⟨G + H, by rw [IntermediateField.coe_add, add_mul, hG, hH, map_add]⟩
  | smul c φ _ hφ =>
    obtain ⟨G, hG⟩ := hφ
    refine ⟨algebraMap F _ c * G, ?_⟩
    rw [IntermediateField.coe_mul, mul_assoc, hG, PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C,
      C_eq_algebraMap']
    rfl

end BridgeMem

end

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (F : Type) [Field F] [CharP F p] (m : ℕ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) F) :
    ∃ G : ↥(modularFunctionFieldC F N),
      (G : LaurentSeries F) * thetaL F (jqModC F) ^ m = HahnSeries.ofPowerSeries ℤ F φ :=
  BridgeMem.main p N hpN F m φ hφ

end S_ModPForms_exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod
end P2MW
export P2MW.S_ModPForms_exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod (solution)
