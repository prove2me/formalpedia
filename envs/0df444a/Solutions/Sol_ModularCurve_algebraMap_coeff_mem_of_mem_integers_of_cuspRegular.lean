-- Prove2me | solution 1 for ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ff2dc10d-4597-5fca-922d-a3fce54a458b

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular
import Theorems.Thm_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular.ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jq jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat"
namespace CM1Aux
p2m_open "ModularCurve"

open HahnSeries IntermediateField AlgebraicCurve IsLocalRing

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

theorem algebraMap_eq_C {L : Type*} [Field L] (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem coe_algebraMap_eq_C {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L)) (c : L) :
    ((algebraMap L F c : F) : LaurentSeries L) = HahnSeries.C c := by
  rw [SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

end ModularCurve.CM1Aux

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular.ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) :
    ∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n) ∈ A := by
  classical
  set L := AlgebraicClosure ℚ with hL
  have hq : (q : ℕ).Prime := Fact.out
  have hAval : A.valuation ((q : ℕ) : L) < 1 := (A.mem_nonunits_iff).mp hA
  have hAq : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have : (((q : ℕ) : ↥A) : L) = (q : L) := by push_cast; rfl
    rw [this]; exact hA

  obtain ⟨c, hc, hcg⟩ := exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular q M' A hA g hg hcusp
  intro n
  by_cases hn0 : g.coeff n = 0
  · rw [hn0, map_zero]; exact zero_mem A

  have hbdd : ∀ k : ℤ, g.coeff k ≠ 0 → -padicValRat q c ≤ padicValRat q (g.coeff k) := by
    intro k hk
    have hmem : ((c * g.coeff k : ℚ) : L) ∈ A := by rw [← eq_ratCast (algebraMap ℚ L)]; exact hcg k
    have h0 := (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hq hAval (mul_ne_zero hc hk)).mp hmem
    rw [padicValRat.mul hc hk] at h0
    linarith
  obtain ⟨m, ⟨k₀, hk₀, hk₀m⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z : ℤ => ∃ k : ℤ, g.coeff k ≠ 0 ∧ padicValRat q (g.coeff k) = z)
    ⟨-padicValRat q c, fun z ⟨k, hk, hkz⟩ => hkz ▸ hbdd k hk⟩ ⟨_, n, hn0, rfl⟩
  have hle : ∀ k : ℤ, g.coeff k ≠ 0 → m ≤ padicValRat q (g.coeff k) := fun k hk => hmin _ ⟨k, hk, rfl⟩
  by_cases hm : 0 ≤ m
  ·
    rw [eq_ratCast]
    exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hq hAval hn0).mpr (hm.trans (hle n hn0))

  exfalso
  have hm' : m < 0 := not_le.mp hm
  clear hm
  have hm : m < 0 := hm'
  obtain ⟨hint, hunit⟩ := coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat (K := L) A hq hA g m hle k₀ hk₀ hk₀m
  set N : ℕ := m.natAbs with hN
  have hNm : ((q : ℚ) ^ m)⁻¹ = (q : ℚ) ^ N := by
    rw [← zpow_neg, ← zpow_natCast]
    congr 1
    rw [hN, Int.ofNat_natAbs_of_nonpos hm.le]
  have hN0 : N ≠ 0 := by
    rw [hN]; exact Int.natAbs_ne_zero.mpr hm.ne
  rw [hNm] at hint hunit

  set h : LaurentSeries ℚ := (q : ℚ) ^ N • g with hh
  have hhF : h ∈ modularFunctionFieldFull M' := by
    rw [hh, ← HahnSeries.C_mul_eq_smul, ← CM1Aux.algebraMap_eq_C]
    exact mul_mem ((modularFunctionFieldFull M').algebraMap_mem _) hg
  let z : LaurentSeries ↥A :=
    { coeff := fun k => ⟨(coeffEmb L h).coeff k, hint k⟩
      isPWO_support' := (coeffEmb L h).isPWO_support'.mono (by
        intro k hk
        simp only [Function.mem_support, ne_eq] at hk ⊢
        exact fun h0 => hk (Subtype.ext h0)) }
  have hz : coeffMap A.subtype z = coeffEmb L h := by ext k; rfl
  have hzF : coeffMap A.subtype z ∈ modularFunctionFieldBar M' := by
    rw [hz]; exact coeffEmb_mem_laurentBaseChange L hhF
  obtain ⟨hzint, hzres⟩ := hR₀ z hzF

  have htA : ((q : L) ^ N) ∈ A := pow_mem (natCast_mem A q) N
  have htint : algebraMap L ↥(modularFunctionFieldBar M') ((q : L) ^ N) ∈ R₀.integers := (R₀.algebraMap_mem_iff _).mpr htA
  have hcoe : coeffEmb L h = HahnSeries.C ((q : L) ^ N) * coeffEmb L g := by
    rw [hh, ← HahnSeries.C_mul_eq_smul, map_mul]
    show coeffMap (algebraMap ℚ L) (HahnSeries.C ((q : ℚ) ^ N)) * coeffEmb L g = _
    rw [CM1Aux.coeffMap_C, map_pow, map_natCast]
  have heq : (⟨_, hzint⟩ : ↥R₀.integers) = ⟨_, htint⟩ * ⟨_, hgi⟩ := by
    apply Subtype.ext; apply Subtype.ext
    show coeffMap A.subtype z = ((algebraMap L ↥(modularFunctionFieldBar M') ((q : L) ^ N) : ↥(modularFunctionFieldBar M')) :
      LaurentSeries L) * coeffEmb L g
    rw [hz, hcoe, CM1Aux.coe_algebraMap_eq_C]
  have hres0 : R₀.residue ⟨_, hzint⟩ = 0 := by
    rw [heq, map_mul]
    have : R₀.residue ⟨_, htint⟩ = algebraMap (ResidueField ↥A) _ (residue ↥A ⟨(q : L) ^ N, htA⟩) :=
      R₀.residue_algebraMap ⟨(q : L) ^ N, htA⟩
    rw [this]
    have hq0 : residue ↥A ⟨(q : L) ^ N, htA⟩ = 0 := by
      have : (⟨(q : L) ^ N, htA⟩ : ↥A) = ((q : ℕ) : ↥A) ^ N := by
        apply Subtype.ext; push_cast; rfl
      rw [this, map_pow, (residue_eq_zero_iff _).mpr hAq, zero_pow hN0]
    rw [hq0, map_zero, zero_mul]

  have hzk : residue ↥A (z.coeff k₀) = 0 := by
    have := congrArg (fun w : LaurentSeries (ResidueField ↥A) => w.coeff k₀) hzres
    simp only [coeffMap_coeff] at this
    rw [← this, hres0]
    rfl
  apply hunit
  have hnu : ((z.coeff k₀ : ↥A) : L) ∈ A.nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr ((residue_eq_zero_iff _).mp hzk)
  exact hnu

end S_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
end P2MW
export P2MW.S_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular (solution)
