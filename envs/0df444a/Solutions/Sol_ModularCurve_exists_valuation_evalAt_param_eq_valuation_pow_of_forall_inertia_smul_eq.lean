-- Prove2me | solution 1 for ModularCurve.exists_valuation_evalAt_param_eq_valuation_pow_of_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/81388456-457d-5e8d-a958-44219d3fcdcb

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
import Theorems.Thm_ValuationSubring_exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing
import Theorems.Thm_GaloisRep_mem_ratLocalizedAt_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_valuation_evalAt_param_eq_valuation_pow_of_forall_inertia_smul_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

namespace AnnInt

theorem algebraMap_mem_of_mem_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (r : ℚ) (hr : r ∈ GaloisRep.ratLocalizedAt p) :
    algebraMap ℚ (AlgebraicClosure ℚ) r ∈ A := by
  have hden : ¬ p ∣ r.den := (GaloisRep.mem_ratLocalizedAt_iff hp.out r).mp hr

  have hdenA : ((r.den : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A r.den
  have hnumA : ((r.num : ℤ) : AlgebraicClosure ℚ) ∈ A := intCast_mem A r.num
  have hunit : IsUnit (⟨((r.den : ℤ) : AlgebraicClosure ℚ), hdenA⟩ : A) := by
    by_contra hnu
    have hm : (⟨((r.den : ℤ) : AlgebraicClosure ℚ), hdenA⟩ : A) ∈ maximalIdeal A := hnu
    have hpm : (⟨((p : ℕ) : AlgebraicClosure ℚ), natCast_mem A p⟩ : A) ∈ maximalIdeal A := by
      have h := hA
      rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at h
      obtain ⟨hpA, hmax⟩ := h
      exact hmax
    have hcop : Nat.Coprime r.den p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hden))
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * r.den + b * p = 1 := by
      have := Int.gcd_eq_gcd_ab (r.den : ℤ) (p : ℤ)
      refine ⟨Int.gcdA r.den p, Int.gcdB r.den p, ?_⟩
      have hg : Int.gcd (r.den : ℤ) (p : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]; exact hcop
      rw [hg] at this
      push_cast at this
      linarith [this]
    have h1 : (1 : A) ∈ maximalIdeal A := by
      have hsum := Ideal.add_mem _ (Ideal.mul_mem_left _ (⟨((a : ℤ) : AlgebraicClosure ℚ), intCast_mem A a⟩ : A) hm)
        (Ideal.mul_mem_left _ (⟨((b : ℤ) : AlgebraicClosure ℚ), intCast_mem A b⟩ : A) hpm)
      have heq : (⟨((a : ℤ) : AlgebraicClosure ℚ), intCast_mem A a⟩ : A) * ⟨((r.den : ℤ) : AlgebraicClosure ℚ), hdenA⟩
          + ⟨((b : ℤ) : AlgebraicClosure ℚ), intCast_mem A b⟩ * ⟨((p : ℕ) : AlgebraicClosure ℚ), natCast_mem A p⟩ = 1 := by
        apply Subtype.ext
        push_cast
        have := congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) hab
        push_cast at this
        exact this
      rw [heq] at hsum
      exact hsum
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hr' : algebraMap ℚ (AlgebraicClosure ℚ) r = ((r.num : ℤ) : AlgebraicClosure ℚ) * (((r.den : ℤ) : AlgebraicClosure ℚ))⁻¹ := by
    rw [eq_ratCast, ← Rat.num_div_den r, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, div_eq_mul_inv]
    simp [Rat.num_div_den]
  rw [hr']
  refine mul_mem hnumA ?_
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hwF : ((r.den : ℤ) : AlgebraicClosure ℚ) * (w : AlgebraicClosure ℚ) = 1 := by
    have := congrArg Subtype.val hw; simpa using this
  have : (((r.den : ℤ) : AlgebraicClosure ℚ))⁻¹ = (w : AlgebraicClosure ℚ) := (eq_inv_of_mul_eq_one_right hwF).symm
  rw [this]; exact w.2

end AnnInt

open AnnInt in
theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (An : AlgebraicCurve.Annulus A ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hz : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • An.param = An.param)
    (V : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) (hV : V ∈ An.dom)
    (hVσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • V = V) :
    ∃ d : ℕ, 1 ≤ d ∧
      A.valuation (V.evalAt An.param) = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ d ∧
      A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) < A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ d := by
  obtain ⟨hrat, hzO, ⟨hcA, hcm⟩, hc0, m, hm, hmod⟩ := An.mem_dom V hV

  have hcfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (V.evalAt An.param) = V.evalAt An.param := by
    intro σ hσ
    have h := ModularCurve.evalAt_eq_apply_evalAt_of_coe_eq_coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F₀ V
      (arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • V) ?_ hrat An.param An.param ?_ hzO
    · rw [hVσ σ hσ] at h
      exact h.symm
    · intro x x' hx'
      have hxx : x' = arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • x :=
        Subtype.ext (hx'.trans (coe_arithmeticGalois_smul _ σ x).symm)
      rw [hxx]
      exact SemilinearAut.ord_smul _ V x
    · rw [← coe_arithmeticGalois_smul _ σ An.param, hz σ hσ]

  let ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A :=
    { toFun := fun r => ⟨algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ), algebraMap_mem_of_mem_ratLocalizedAt p A hA r r.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) := by
    apply RingHom.ext; intro r; rfl
  obtain ⟨ι, ρO, hι, -, hinj, hDVR, hmax, hmiff, -, -⟩ :=
    ValuationSubring.exists_ringHom_comap_fixedField_inertiaSubgroupIn_comp_eq_and_isDiscreteValuationRing p A hA ρ hρ
  set c : AlgebraicClosure ℚ := V.evalAt An.param with hc
  have hcF : c ∈ IntermediateField.fixedField (A.inertiaSubgroupIn ℚ) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ; exact hcfix σ hσ
  set cF : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) := ⟨c, hcF⟩ with hcF'
  have hcO : cF ∈ A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)) := by
    rw [ValuationSubring.mem_comap]
    exact hcA
  set o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) := ⟨cF, hcO⟩ with ho
  have hιo : ((ι o : ↥A) : AlgebraicClosure ℚ) = c := hι o
  have hιo' : ι o = ⟨c, hcA⟩ := Subtype.ext hιo
  have homax : o ∈ maximalIdeal _ := (hmiff o).mp (by rw [hιo']; exact hcm)
  haveI := hDVR
  have hirr : Irreducible (((p : ℕ)) : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have ho0 : o ≠ 0 := by
    intro h0
    apply hc0
    have : ι o = 0 := by rw [h0, map_zero]
    rw [hιo'] at this
    exact congrArg Subtype.val this
  obtain ⟨d, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hirr

  have hd : 1 ≤ d := by
    by_contra hd0
    have hd0' : d = 0 := by omega
    rw [hd0', pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).mp homax (hu ▸ u.isUnit)

  have hvu : A.valuation ((ι (u : _) : ↥A) : AlgebraicClosure ℚ) = 1 := by
    have hU : IsUnit (ι (u : _)) := u.isUnit.map ι
    obtain ⟨w, hw⟩ := hU
    rw [← hw]
    exact A.valuation_unit w
  have hvc : A.valuation c = A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ d := by
    have h1 : c = ((ι (u : _) : ↥A) : AlgebraicClosure ℚ) * ((p : ℕ) : AlgebraicClosure ℚ) ^ d := by
      rw [← hιo, hu, map_mul, map_pow, map_natCast]
      push_cast
      ring
    rw [h1, map_mul, map_pow, hvu, one_mul]
  refine ⟨d, hd, hvc, ?_⟩

  have hvm : A.valuation (m : AlgebraicClosure ℚ) < 1 := (ValuationSubring.valuation_lt_one_iff A m).mp hm
  have hvc0 : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
  rw [hmod, map_mul, ← hvc]
  calc A.valuation c * A.valuation (m : AlgebraicClosure ℚ) < A.valuation c * 1 :=
        mul_lt_mul_of_pos_left hvm (zero_lt_iff.mpr hvc0)
    _ = A.valuation c := mul_one _

end S_ModularCurve_exists_valuation_evalAt_param_eq_valuation_pow_of_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_exists_valuation_evalAt_param_eq_valuation_pow_of_forall_inertia_smul_eq (solution)
