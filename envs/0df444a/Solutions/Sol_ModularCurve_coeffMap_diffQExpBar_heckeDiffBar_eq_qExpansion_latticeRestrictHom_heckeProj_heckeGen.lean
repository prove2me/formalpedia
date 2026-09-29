-- Prove2me | solution 1 for ModularCurve.coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/efda12f5-8504-51e3-9f78-34fe1d7e218a

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd
import Theorems.Thm_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve CuspForm

namespace EquivQ

theorem coeff_ofPowerSeries_neg (x : PowerSeries ℂ) {m : ℤ} (hm : m < 0) :
    (HahnSeries.ofPowerSeries ℤ ℂ x).coeff m = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  simp only [Set.mem_range, RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, not_exists]
  intro k hk
  rw [Nat.castOrderEmbedding_apply] at hk
  omega

theorem coeff_ofPowerSeries_natCast (x : PowerSeries ℂ) (k : ℕ) :
    (HahnSeries.ofPowerSeries ℤ ℂ x).coeff (k : ℤ) = PowerSeries.coeff k x :=
  HahnSeries.ofPowerSeries_apply_coeff x k

end EquivQ

theorem solution
    (N : ℕ) [NeZero N] (ι₀ : AlgebraicClosure ℚ →+* ℂ) (ℓ : Nat.Primes)
    (η : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (f : ↥(CuspForm.intLattice N 2))
    (h : coeffMap ι₀ (diffQExpBar N η) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2))) :
    coeffMap ι₀ (diffQExpBar N (heckeDiffBar N ℓ η)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
        (((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val f :
            ↥(CuspForm.intLattice N 2)) : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N
  have hβ := ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) N ℓ
  have hℓ0 : (ℓ : ℕ) ≠ 0 := ℓ.2.ne_zero

  have hU : ∀ (hℓN : (ℓ : ℕ) ∣ N) (n : ℤ), (diffQExpBar N (heckeDiffBar N ℓ η)).coeff n =
      (diffQExpBar N η).coeff (n * (ℓ : ℕ)) :=
    fun hℓN n => coeff_diffQExpBar_heckeDiffBar_of_dvd N ℓ hℓN η n
  have hT : ∀ (hℓN : ¬ (ℓ : ℕ) ∣ N) (n : ℤ), (diffQExpBar N (heckeDiffBar N ℓ η)).coeff n =
      (diffQExpBar N η).coeff (n * (ℓ : ℕ)) +
        ((ℓ : ℕ) : AlgebraicClosure ℚ) * (if ((ℓ : ℕ) : ℤ) ∣ n then (diffQExpBar N η).coeff (n / (ℓ : ℕ)) else 0) :=
    fun hℓN n => coeff_diffQExpBar_heckeDiffBar_of_not_dvd N ℓ hℓN hβ η n

  have hR : ((((((CuspForm.latticeRestrictHom N ∅).toRingHom.comp (heckeProj N)) (heckeGen ℓ)).val f :
        ↥(CuspForm.intLattice N 2)) : CuspForm (CongruenceSubgroup.Gamma0 N) 2))
      = (if hd : (ℓ : ℕ) ∣ N then CuspForm.heckeULin 2 hd else CuspForm.heckeTLin 2 ℓ.2 hd)
          (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
    change ((heckeProj N (heckeGen ℓ) : ↥(CuspForm.heckeAlgebra N 2 ∅)) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) = _
    by_cases hd : (ℓ : ℕ) ∣ N
    · rw [dif_pos hd, heckeProj_heckeGen_of_dvd ℓ hd, CuspForm.heckeAlgebra.coe_U]
    · rw [dif_neg hd, heckeProj_heckeGen_of_not_dvd ℓ hd, CuspForm.heckeAlgebra.coe_T]
  rw [hR]

  have hcoe : ∀ m : ℤ, ι₀ ((diffQExpBar N η).coeff m) =
      (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1
        ⇑(f : CuspForm (CongruenceSubgroup.Gamma0 N) 2))).coeff m := fun m => by
    rw [← coeffMap_coeff, h]
  have hq : ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (k : ℕ),
      (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)).coeff (k : ℤ) =
        ModularFormClass.qCoeff ⇑g k := fun g k => EquivQ.coeff_ofPowerSeries_natCast _ k

  refine HahnSeries.ext (funext fun n => ?_)
  rw [coeffMap_coeff]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  ·
    by_cases hd : (ℓ : ℕ) ∣ N
    · rw [dif_pos hd, hU hd, hq, CuspForm.coe_heckeULin_apply,
        ModularFormClass.qCoeff_heckeU _ hΓ hℓ0, ModularForm.coeffHeckeU_apply,
        show ((k : ℤ) * (ℓ : ℕ) : ℤ) = ((k * ℓ : ℕ) : ℤ) by push_cast; ring, hcoe, hq]
    · rw [dif_neg hd, hT hd, map_add, map_mul,
        map_natCast, apply_ite ι₀, map_zero,
        show ((k : ℤ) * (ℓ : ℕ) : ℤ) = ((k * ℓ : ℕ) : ℤ) by push_cast; ring, hcoe, hq, hq,
        CuspForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT _ hΓ hℓ0, ModularForm.coeffHeckeT_apply]
      have hdvd : ((ℓ : ℕ) : ℤ) ∣ (k : ℤ) ↔ (ℓ : ℕ) ∣ k := Int.natCast_dvd_natCast
      by_cases hk : (ℓ : ℕ) ∣ k
      · rw [if_pos (hdvd.mpr hk), if_pos hk, show ((k : ℤ) / (ℓ : ℕ) : ℤ) = ((k / ℓ : ℕ) : ℤ) by push_cast; rfl,
          hcoe, hq]
        congr 1
        simp only [zpow_one, Int.reduceSub]
      · rw [if_neg (fun h' => hk (hdvd.mp h')), if_neg hk, mul_zero]
  ·
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.cast_zero, neg_zero]
      by_cases hd : (ℓ : ℕ) ∣ N
      · rw [dif_pos hd, hU hd, zero_mul, hcoe]
        rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, hq, hq, CuspForm.coe_heckeULin_apply,
          ModularFormClass.qCoeff_heckeU _ hΓ hℓ0, ModularForm.coeffHeckeU_apply, zero_mul]
      · rw [dif_neg hd, hT hd, zero_mul,
          if_pos (dvd_zero _), EuclideanDomain.zero_div, map_add, map_mul, map_natCast, hcoe,
          show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, hq, hq, CuspForm.coe_heckeTLin_apply,
          ModularFormClass.qCoeff_heckeT _ hΓ hℓ0, ModularForm.coeffHeckeT_apply, if_pos (dvd_zero _),
          zero_mul, Nat.zero_div]
        congr 1
        simp only [zpow_one, Int.reduceSub]
    · have hneg : (-(k : ℤ)) < 0 := by omega
      rw [EquivQ.coeff_ofPowerSeries_neg _ hneg]
      have hℓpos : (0 : ℤ) < (ℓ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hℓ0
      by_cases hd : (ℓ : ℕ) ∣ N
      · rw [hU hd, hcoe, EquivQ.coeff_ofPowerSeries_neg _ (by nlinarith)]
      · rw [hT hd, map_add, map_mul,
          map_natCast, apply_ite ι₀, map_zero, hcoe, EquivQ.coeff_ofPowerSeries_neg _ (by nlinarith), zero_add]
        by_cases hdv : ((ℓ : ℕ) : ℤ) ∣ (-(k : ℤ))
        · rw [if_pos hdv, hcoe, EquivQ.coeff_ofPowerSeries_neg _ (Int.ediv_neg_of_neg_of_pos hneg hℓpos), mul_zero]
        · rw [if_neg hdv, mul_zero]

end S_ModularCurve_coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen
end P2MW
export P2MW.S_ModularCurve_coeffMap_diffQExpBar_heckeDiffBar_eq_qExpansion_latticeRestrictHom_heckeProj_heckeGen (solution)
