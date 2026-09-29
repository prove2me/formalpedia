-- Prove2me | solution 1 for ModularCurve.exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/85799f22-0db8-52c3-a1d3-705c5e3059b8

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace Ws49
namespace CSlack

section Constants

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem coe_algebraMap (a : (AlgebraicClosure ℚ)) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.C a := by
  rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a from
    (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ)) a).symm, HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]

theorem not_mem_range_of_coeff_ne_zero {x : ↥(xHFunctionFieldBar M H)} {n : ℤ} (hn : n ≠ 0) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ≠ 0) :
    x ∉ Set.range (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := by
  rintro ⟨a, rfl⟩
  apply hx
  rw [coe_algebraMap, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn]

theorem transcendental_of_coeff_ne_zero {x : ↥(xHFunctionFieldBar M H)} {n : ℤ} (hn : n ≠ 0) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ≠ 0) :
    Transcendental (AlgebraicClosure ℚ) x := by
  intro halg
  apply not_mem_range_of_coeff_ne_zero hn hx
  have hint : IsIntegral (AlgebraicClosure ℚ) x := halg.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible (AlgebraicClosure ℚ) (minpoly.irreducible hint)
  obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
  exact ⟨a, ha⟩

theorem mem_range_of_forall_ord_eq_zero {g : ↥(xHFunctionFieldBar M H)} (hg : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord g = 0) :
    g ∈ Set.range (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := by
  obtain ⟨hcurve, hess⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H
  haveI := hess
  haveI := hcurve
  obtain ⟨t, ht, hfin, -⟩ := (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional
    (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))).mp hcurve
  haveI := hfin
  have hconst : ConstantsAreBase (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hmem : g ∈ LSpace (0 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := by
    rw [mem_lSpace_iff_ord]
    exact Or.inr fun v => by rw [hg v]; simp
  rw [ConstantsAreBase] at hconst
  rw [hconst] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩

end Constants

end Ws49.CSlack

open Ws49.CSlack in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D D' : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (hDD' : (Pic0.mk D : JH M H) = Pic0.mk D')
    (f f' : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0) (hf' : f' ≠ 0)
    (hdivf : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord f)
    (hdivf' : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord f') :
    ∃ (h : ↥(xHFunctionFieldBar M H)) (c₀ : AlgebraicClosure ℚ), h ≠ 0 ∧ c₀ ≠ 0 ∧
      (∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) v = (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) v + v.ord h) ∧
      f' = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c₀ * f * (wgen • h) ^ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hprin : ((D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - (D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) ∈ Divisor.principal (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H)) := by
    have h := (QuotientAddGroup.eq (s := (Divisor.principal (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))).addSubgroupOf (Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))))).mp hDD'.symm
    rw [AddSubgroup.mem_addSubgroupOf] at h
    simpa [sub_eq_neg_add] using h
  obtain ⟨k, hk0, hk⟩ := hprin

  set u : ↥(xHFunctionFieldBar M H) := f * (wgen • k⁻¹) ^ p with hu
  have hwk0 : wgen • k⁻¹ ≠ (0 : ↥(xHFunctionFieldBar M H)) := by
    rw [SemilinearAut.smul_def]; exact (map_ne_zero _).mpr (inv_ne_zero hk0)
  have hu0 : u ≠ 0 := mul_ne_zero hf (pow_ne_zero _ hwk0)

  have hord : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.ord u = v.ord f' := by
    intro v
    have h1 : v.ord (wgen • k⁻¹) = (wgen⁻¹ • v).ord k⁻¹ := by
      have := SemilinearAut.ord_smul wgen (wgen⁻¹ • v) k⁻¹
      rwa [smul_inv_smul] at this
    rw [hu, v.ord_mul hf (pow_ne_zero _ hwk0), ← zpow_natCast, v.ord_zpow, h1, (wgen⁻¹ • v).ord_inv, ← hdivf v, ← hdivf' v]
    have hkv := hk (wgen⁻¹ • v)
    simp only [Finsupp.coe_sub, Pi.sub_apply] at hkv
    rw [SemilinearAut.divisor_smul_apply, SemilinearAut.divisor_smul_apply, ← hkv]
    push_cast
    ring

  obtain ⟨c₀, hc₀⟩ := mem_range_of_forall_ord_eq_zero (M := M) (H := H) (g := f' / u) fun v => by
    rw [div_eq_mul_inv, v.ord_mul hf' (inv_ne_zero hu0), v.ord_inv, hord v]; ring
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, div_eq_zero_iff] at hc₀
    exact hc₀.elim hf' hu0
  refine ⟨k⁻¹, c₀, inv_ne_zero hk0, hc₀0, fun v => ?_, ?_⟩
  · have hkv := hk v
    simp only [Finsupp.coe_sub, Pi.sub_apply] at hkv
    rw [v.ord_inv, ← hkv]; ring
  · rw [mul_assoc, ← hu, hc₀, div_mul_cancel₀ _ hu0]

end S_ModularCurve_exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
end P2MW
export P2MW.S_ModularCurve_exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq (solution)
