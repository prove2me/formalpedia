-- Prove2me | solution 1 for ModularCurve.JZero.exists_isRepOf_forall_apply_cuspInftyBar_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/14ed0b62-003c-5c9b-b794-d00a25e1b256

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_cuspInftyBar
import Theorems.Thm_ModularCurve_finrank_riemannRochSpace_eq_one_of_sub_single_eq_bot
import Theorems.Thm_ModularCurve_eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one
import Theorems.Thm_ModularCurve_JZero_isPrincipal_sub_of_isRepOf
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_isRepOf_forall_apply_cuspInftyBar_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

open ModularCurve.JZero in
theorem solution (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (n : ℕ)
    (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
    (hc : ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K n c D) :
    ∃ D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K n c D' ∧
      riemannRochSpace (D'.erase (cuspInftyBar N) - Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ ∧
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K n c D →
        D (cuspInftyBar N) ≤ D' (cuspInftyBar N) := by
  classical
  obtain ⟨D, hD⟩ := hc
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    isCurveOver_modularFunctionFieldBar N
  obtain ⟨E, hDeff, hshape, hstab, hcE⟩ := hD

  have hs1 : (Finsupp.single (cuspInftyBar N) (1 : ℤ)) (cuspInftyBar N) = 1 := Finsupp.single_eq_same
  have hs0 : ∀ w, w ≠ cuspInftyBar N → (Finsupp.single (cuspInftyBar N) (1 : ℤ)) w = 0 := by
    intro w hw
    exact Finsupp.single_eq_of_ne hw
  have hdeg1 : ((cuspInftyBar N).deg : ℤ) = 1 := by
    rw [deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), Nat.cast_one]
  have hE0 : Divisor.degree (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = 0 := E.2
  have hdegD : Divisor.degree D = n := by
    rw [← hshape, map_add, hE0, map_zsmul, Divisor.degree_single, hdeg1]
    simp

  let Pj : ℕ → Prop := fun j =>
    riemannRochSpace (D - (j : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) ≠ ⊥
  haveI hdec : DecidablePred Pj := fun _ => Classical.propDecidable _
  have hone : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace D :=
    mem_riemannRochSpace_iff.mpr fun w => Or.inr (by rw [Place.ord_one]; linarith [hDeff w])
  have hP0 : Pj 0 := by
    show riemannRochSpace (D - ((0 : ℕ) : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) ≠ ⊥
    rw [Nat.cast_zero, zero_smul, sub_zero]
    intro hbot
    rw [hbot, Submodule.mem_bot] at hone
    exact one_ne_zero hone
  obtain ⟨k, hk, hkmax⟩ : ∃ k : ℕ, Pj k ∧ ∀ j : ℕ, k < j → j ≤ n → ¬ Pj j :=
    ⟨Nat.findGreatest Pj n, Nat.findGreatest_spec (Nat.zero_le n) hP0,
      fun j hj hjn => Nat.findGreatest_is_greatest hj hjn⟩
  have hgt : ∀ j : ℕ, k < j →
      riemannRochSpace (D - (j : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ := by
    intro j hj
    by_cases hjn : j ≤ n
    · have := hkmax j hj hjn
      simpa [Pj] using this
    · have hjn' : n < j := lt_of_not_ge hjn
      apply lSpace_eq_bot_of_degree_neg
      rw [map_sub, map_zsmul, Divisor.degree_single, hdegD, hdeg1]
      simp only [smul_eq_mul, mul_one]
      omega

  obtain ⟨f, hfmem, hf0⟩ := (Submodule.ne_bot_iff _).mp hk
  have hford : ∀ w, -(D - ((k : ℕ) : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) w
      ≤ w.ord f :=
    fun w => ((mem_riemannRochSpace_iff.mp hfmem) w).resolve_left hf0
  obtain ⟨P, hPw, hPdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
  have hPprin : P ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
    ⟨f, hf0, hPw⟩

  have hD'eff : ∀ w, 0 ≤ (D + P) w := by
    intro w
    have h1 := hford w
    rw [Finsupp.sub_apply, neg_sub, Finsupp.smul_apply, smul_eq_mul] at h1
    rw [Finsupp.add_apply, hPw w]
    by_cases hw : w = cuspInftyBar N
    · subst hw; rw [hs1] at h1; have : (0 : ℤ) ≤ (k : ℕ) := Nat.cast_nonneg _; linarith
    · rw [hs0 w hw, mul_zero] at h1; linarith
  have herase_eff : 0 ≤ (D + P).erase (cuspInftyBar N) := by
    intro w
    by_cases hw : w = cuspInftyBar N
    · subst hw; simp
    · rw [Finsupp.erase_ne hw]; exact hD'eff w

  have hbot : riemannRochSpace ((D + P).erase (cuspInftyBar N)
      - Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro h hh
    by_contra hh0
    have hhord : ∀ w, -((D + P).erase (cuspInftyBar N) - Finsupp.single (cuspInftyBar N) (1 : ℤ)) w
        ≤ w.ord h :=
      fun w => ((mem_riemannRochSpace_iff.mp hh) w).resolve_left hh0
    have hk'0 : 0 ≤ (D + P) (cuspInftyBar N) := hD'eff _
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = (D + P) (cuspInftyBar N) + 1 :=
      ⟨((D + P) (cuspInftyBar N) + 1).toNat, Int.toNat_of_nonneg (by linarith)⟩
    have hkj : k < j := by
      have h1 := hford (cuspInftyBar N)
      rw [Finsupp.sub_apply, neg_sub, Finsupp.smul_apply, smul_eq_mul, hs1, mul_one] at h1
      have h2 : (D + P) (cuspInftyBar N) = D (cuspInftyBar N) + (cuspInftyBar N).ord f := by
        rw [Finsupp.add_apply, hPw]
      have : ((k : ℕ) : ℤ) < j := by rw [hj]; linarith
      exact_mod_cast this
    have hprod : h * f ∈ riemannRochSpace
        (D - (j : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) := by
      refine mem_riemannRochSpace_iff.mpr fun w => Or.inr ?_
      rw [Place.ord_mul w hh0 hf0, ← hPw w, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
      have a1 := hhord w
      rw [Finsupp.sub_apply] at a1
      by_cases hw : w = cuspInftyBar N
      · subst hw
        rw [Finsupp.erase_same, hs1] at a1
        rw [hs1, mul_one]
        have a3 : P (cuspInftyBar N) = (D + P) (cuspInftyBar N) - D (cuspInftyBar N) := by
          rw [Finsupp.add_apply]; ring
        rw [a3]
        linarith [hj, a1]
      · rw [Finsupp.erase_ne hw, Finsupp.add_apply, hs0 w hw] at a1
        rw [hs0 w hw, mul_zero]
        linarith
    rw [hgt j hkj, Submodule.mem_bot] at hprod
    exact (mul_ne_zero hh0 hf0) hprod

  have hB : Module.finrank (AlgebraicClosure ℚ)
      ↥(riemannRochSpace ((D + P).erase (cuspInftyBar N))) = 1 :=
    finrank_riemannRochSpace_eq_one_of_sub_single_eq_bot N herase_eff (cuspInftyBar N) hbot

  have hrep' : JZero.IsRepOf N K n c (D + P) := by
    refine ⟨⟨(E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) + P, add_mem E.2 hPdeg⟩,
      hD'eff, ?_, ?_, ?_⟩
    · show ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) + P)
        + (n : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D + P
      rw [← hshape]; abel
    · intro σ hσ
      have hgD : arithmeticGalois (modularFunctionFieldFull N) σ • D = D := hstab σ hσ
      have hginv : (arithmeticGalois (modularFunctionFieldFull N) σ)⁻¹ • cuspInftyBar N = cuspInftyBar N := by
        rw [inv_smul_eq_iff, arithmeticGalois_smul_cuspInftyBar N σ]
      have hQ : arithmeticGalois (modularFunctionFieldFull N) σ • P - P
          ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
        sub_mem (SemilinearAut.smul_mem_principal _ hPprin) hPprin
      obtain ⟨h, hh0, hhQ⟩ := hQ
      have hgD' : arithmeticGalois (modularFunctionFieldFull N) σ • (D + P)
          = (D + P) + (arithmeticGalois (modularFunctionFieldFull N) σ • P - P) := by
        rw [smul_add, hgD]; abel
      have hgeff : ∀ w, 0 ≤ (arithmeticGalois (modularFunctionFieldFull N) σ • (D + P)) w := fun w => by
        rw [SemilinearAut.divisor_smul_apply]; exact hD'eff _
      have hcusp : (arithmeticGalois (modularFunctionFieldFull N) σ • (D + P)) (cuspInftyBar N)
          = (D + P) (cuspInftyBar N) := by
        rw [SemilinearAut.divisor_smul_apply, hginv]
      have hE1 : (arithmeticGalois (modularFunctionFieldFull N) σ • (D + P)).erase (cuspInftyBar N)
          = (D + P).erase (cuspInftyBar N) := by
        refine eq_of_isPrincipal_sub_of_finrank_riemannRochSpace_eq_one N herase_eff ?_ hB ?_
        · intro w
          by_cases hw : w = cuspInftyBar N
          · subst hw; simp
          · rw [Finsupp.erase_ne hw]; exact hgeff w
        · refine ⟨h, hh0, fun w => ?_⟩
          rw [← hhQ w]
          have e := DFunLike.congr_fun hgD' w
          rw [Finsupp.add_apply] at e
          by_cases hw : w = cuspInftyBar N
          · subst hw
            rw [Finsupp.sub_apply, Finsupp.erase_same, Finsupp.erase_same, sub_self]
            linarith [hcusp]
          · rw [Finsupp.sub_apply, Finsupp.erase_ne hw, Finsupp.erase_ne hw]
            linarith
      ext w
      by_cases hw : w = cuspInftyBar N
      · subst hw; exact hcusp
      · have e := congrArg (fun X => X w) hE1
        simp only [Finsupp.erase_ne hw] at e
        exact e
    · rw [← hcE]
      apply QuotientAddGroup.eq.mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      show -((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) + P)
        + (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) ∈ Divisor.principal
      have : -((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) + P)
          + (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = -P := by abel
      rw [this]
      exact neg_mem hPprin

  refine ⟨D + P, hrep', hbot, fun D'' hD'' => ?_⟩
  by_contra hlt
  have hlt' := lt_of_not_ge hlt
  obtain ⟨h, hh0, hh⟩ := isPrincipal_sub_of_isRepOf N K hrep' hD''
  obtain ⟨E'', hD''eff, -, -, -⟩ := hD''
  have hmem : h ∈ riemannRochSpace ((D + P).erase (cuspInftyBar N)
      - Finsupp.single (cuspInftyBar N) (1 : ℤ)) := by
    refine mem_riemannRochSpace_iff.mpr fun w => Or.inr ?_
    rw [← hh w, Finsupp.sub_apply, Finsupp.sub_apply]
    by_cases hw : w = cuspInftyBar N
    · subst hw
      rw [Finsupp.erase_same, hs1]
      linarith
    · rw [Finsupp.erase_ne hw, hs0 w hw]
      linarith [hD''eff w]
  rw [hbot, Submodule.mem_bot] at hmem
  exact hh0 hmem

end S_ModularCurve_JZero_exists_isRepOf_forall_apply_cuspInftyBar_le
end P2MW
export P2MW.S_ModularCurve_JZero_exists_isRepOf_forall_apply_cuspInftyBar_le (solution)
