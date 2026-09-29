-- Prove2me | solution 1 for ModularCurve.exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7b0db498-2e7a-5b82-a752-17bb37764375

import Mathlib
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

open AlgebraicCurve ModularCurve

noncomputable section

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (g : ↥(modularFunctionFieldFull N))
    (hg : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), W ≠ cuspInftyBar N →
      0 ≤ W.ord (⟨coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) g.2⟩ : ↥(modularFunctionFieldBar N))) :
    ∃ M : ℕ, ∀ m : ℤ, 0 ≤ padicValRat p ((p : ℚ) ^ M * (g : LaurentSeries ℚ).coeff m) := by
  classical
  have hp : p.Prime := Fact.out

  set f : ↥(modularFunctionFieldBar N) := ⟨coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) g.2⟩ with hfdef
  have hcoef : ∀ m : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff m
      = (((g : LaurentSeries ℚ).coeff m : ℚ) : AlgebraicClosure ℚ) := fun m => by
    show (coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ)).coeff m = _
    rw [coeffEmb_coeff, eq_ratCast]
  by_cases hg0 : (g : LaurentSeries ℚ) = 0
  · refine ⟨0, fun m => ?_⟩
    rw [hg0, HahnSeries.coeff_zero, mul_zero, padicValRat.zero]
  have hf0 : f ≠ 0 := by
    intro h0
    apply hg0
    ext m
    have h1 : (f : LaurentSeries (AlgebraicClosure ℚ)).coeff m = 0 := by rw [h0]; rfl
    rw [hcoef] at h1
    rw [HahnSeries.coeff_zero]
    exact_mod_cast h1

  set n : ℕ := (-((cuspInftyBar N).ord f)).toNat with hn
  have hfL : f ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) := by
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hv : cuspInftyBar N = v
    · subst hv
      rw [if_pos rfl, mul_one, hn]
      have := Int.self_le_toNat (-((cuspInftyBar N).ord f))
      omega
    · rw [if_neg hv, mul_zero, neg_zero]
      exact hg v (fun h => hv h.symm)

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
  have hAq : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hA
  obtain ⟨c, hc0, hint, k₀, hk₀⟩ :=
    ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits N n f hfL hf0 A hp hA

  set a : ℤ → ℚ := fun m => (g : LaurentSeries ℚ).coeff m with ha
  have hcf : ∀ m : ℤ, ((c • f : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)).coeff m
      = c * ((a m : ℚ) : AlgebraicClosure ℚ) := fun m => by
    rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
      HahnSeries.coeff_single_zero_mul, hcoef]

  have hu : c * ((a k₀ : ℚ) : AlgebraicClosure ℚ) ∉ A.nonunits := by rw [← hcf]; exact hk₀
  have hak₀ : a k₀ ≠ 0 := by
    intro h0
    apply hu
    rw [h0, Rat.cast_zero, mul_zero, ValuationSubring.mem_nonunits_iff, map_zero]
    exact zero_lt_one
  have huinv : (c * ((a k₀ : ℚ) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
    have hle : A.valuation (c * ((a k₀ : ℚ) : AlgebraicClosure ℚ)) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr (by rw [← hcf]; exact hint k₀)
    have hnlt : ¬ A.valuation (c * ((a k₀ : ℚ) : AlgebraicClosure ℚ)) < 1 := fun h =>
      hu ((ValuationSubring.mem_nonunits_iff _).mpr h)
    have heq : A.valuation (c * ((a k₀ : ℚ) : AlgebraicClosure ℚ)) = 1 := le_antisymm hle (not_lt.mp hnlt)
    apply (A.valuation_le_one_iff _).mp
    rw [map_inv₀, heq, inv_one]

  have hval : ∀ m : ℤ, a m ≠ 0 → padicValRat p (a k₀) ≤ padicValRat p (a m) := by
    intro m hm
    have hmem : (((a m / a k₀ : ℚ)) : AlgebraicClosure ℚ) ∈ A := by
      have : (((a m / a k₀ : ℚ)) : AlgebraicClosure ℚ)
          = (c * ((a m : ℚ) : AlgebraicClosure ℚ)) * (c * ((a k₀ : ℚ) : AlgebraicClosure ℚ))⁻¹ := by
        have hk : ((a k₀ : ℚ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hak₀
        push_cast
        field_simp
      rw [this]
      exact mul_mem (by rw [← hcf]; exact hint m) huinv
    have hdiv : a m / a k₀ ≠ 0 := div_ne_zero hm hak₀
    have h0 := (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAq hdiv).mp hmem
    rw [padicValRat.div hm hak₀] at h0
    linarith

  refine ⟨(-(padicValRat p (a k₀))).toNat, fun m => ?_⟩
  by_cases hm : a m = 0
  · show 0 ≤ padicValRat p ((p : ℚ) ^ _ * a m)
    rw [hm, mul_zero, padicValRat.zero]
  · show 0 ≤ padicValRat p ((p : ℚ) ^ _ * a m)
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.mul (pow_ne_zero _ hpq) hm, padicValRat.pow _, padicValRat.self hp.one_lt]
    have h1 := hval m hm
    have h2 := Int.self_le_toNat (-(padicValRat p (a k₀)))
    push_cast
    omega

end

end S_ModularCurve_exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg
end P2MW
export P2MW.S_ModularCurve_exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg (solution)
