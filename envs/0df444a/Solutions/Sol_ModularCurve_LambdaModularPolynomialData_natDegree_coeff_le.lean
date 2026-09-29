-- Prove2me | solution 1 for ModularCurve.LambdaModularPolynomialData.natDegree_coeff_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f47ac580-fbf3-5ec3-8e04-0b3af0c00e28

import Mathlib
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Theorems.Thm_ModularCurve_LambdaModularPolynomialData_eval2_swap_eq_zero
import Theorems.Thm_ModularCurve_minpoly_lambdaNModC_eq
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

open ModularCurve Polynomial

namespace LambdaXdegSol

section Swap

variable (R : Type*) [CommRing R]

def inner : Polynomial R →+* Polynomial (Polynomial R) := Polynomial.mapRingHom (Polynomial.C : R →+* Polynomial R)

def swap : Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (inner R) (Polynomial.C Polynomial.X)

variable {R}

@[scoped simp] theorem inner_C (r : R) : inner R (C r) = C (C r) := by simp [inner]
@[scoped simp] theorem inner_X : inner R X = X := by simp [inner]
@[scoped simp] theorem swap_C (p : Polynomial R) : swap R (C p) = inner R p := by simp [swap]
@[scoped simp] theorem swap_X : swap R X = C X := by simp [swap]

theorem swap_C_C (r : R) : swap R (C (C r)) = C (C r) := by rw [swap_C, inner_C]
theorem swap_C_X : swap R (C X) = X := by rw [swap_C, inner_X]

theorem swap_swap (P : Polynomial (Polynomial R)) : swap R (swap R P) = P := by
  have h : (swap R).comp (swap R) = RingHom.id _ := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine Polynomial.ringHom_ext' ?_ ?_
      · ext r; simp [swap_C_C]
      · simp [swap_C_X]
    · simp [swap_C_X]
  exact congrArg (fun φ => φ P) h

theorem coeff_coeff_swap (P : Polynomial (Polynomial R)) (i k : ℕ) :
    ((swap R P).coeff i).coeff k = (P.coeff k).coeff i := by

  have hP : swap R P = P.sum (fun b a => inner R a * (C X) ^ b) := by
    rw [swap, coe_eval₂RingHom, eval₂_def]
  rw [hP, Polynomial.sum_def, finset_sum_coeff, finset_sum_coeff]
  have hterm : ∀ b : ℕ, ((inner R (P.coeff b) * C X ^ b).coeff i).coeff k = if b = k then (P.coeff k).coeff i else 0 := by
    intro b
    rw [← C_pow, mul_comm, coeff_C_mul, inner, coe_mapRingHom, coeff_map, coeff_mul_C, coeff_X_pow]
    by_cases h : b = k
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, zero_mul]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq' P.support k]
  split_ifs with hk
  · rfl
  · rw [Polynomial.notMem_support_iff.mp hk]; simp

theorem natDegree_coeff_le_natDegree_swap (P : Polynomial (Polynomial R)) (k : ℕ) :
    (P.coeff k).natDegree ≤ (swap R P).natDegree := by
  by_cases h0 : P.coeff k = 0
  · rw [h0, natDegree_zero]; exact Nat.zero_le _
  refine le_natDegree_of_ne_zero (fun h => ?_)
  have h1 : ((swap R P).coeff (P.coeff k).natDegree).coeff k = 0 := by rw [h, coeff_zero]
  rw [coeff_coeff_swap] at h1
  exact (leadingCoeff_ne_zero.mpr h0) h1

def ev2 {A : Type*} [CommRing A] [Algebra R A] (P : Polynomial (Polynomial R)) (x y : A) : A :=
  P.eval₂ (Polynomial.eval₂RingHom (algebraMap R A) x) y

theorem ev2_swap {A : Type*} [CommRing A] [Algebra R A] (P : Polynomial (Polynomial R)) (x y : A) :
    ev2 (swap R P) x y = ev2 P y x := by
  have h : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap R A) x) y).comp (swap R)
      = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap R A) y) x := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine Polynomial.ringHom_ext' ?_ ?_
      · ext r; simp [swap_C_C]
      · simp [swap_C_X]
    · simp [swap_X]
  exact congrArg (fun φ => φ P) h

end Swap

variable (q : ℕ) [hq : Fact q.Prime]

scoped instance : NeZero q := ⟨hq.out.ne_zero⟩

local notation "L" => LaurentSeries ℚ
local notation "μ" => lambdaModC ℚ
local notation "μq" => lambdaNModC ℚ q

def PsiQ (data : LambdaModularPolynomialData q) : Polynomial (Polynomial ℚ) :=
  data.Ψ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem PsiQ_monic (data : LambdaModularPolynomialData q) : (PsiQ q data).Monic := data.monic.map _

theorem PsiQ_natDegree (data : LambdaModularPolynomialData q) : (PsiQ q data).natDegree = q + 1 := by
  rw [PsiQ, data.monic.natDegree_map, data.natDegree_eq]

theorem ev2_PsiQ (data : LambdaModularPolynomialData q) (x y : L) :
    ev2 (PsiQ q data) x y = data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom L) x) y := by
  rw [ev2, PsiQ, eval₂_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem ev2_swap_PsiQ (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    ev2 (swap ℚ (PsiQ q data)) μ μq = 0 := by
  rw [ev2_swap, ev2_PsiQ]
  exact ModularCurve.LambdaModularPolynomialData.eval2_swap_eq_zero q hq2 data

abbrev Fμ : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set L)

def muF : Fμ := ⟨lambdaModC ℚ, IntermediateField.mem_adjoin_simple_self ℚ (lambdaModC ℚ)⟩

def toF : Polynomial ℚ →+* Fμ := (Polynomial.aeval (R := ℚ) muF).toRingHom

theorem toF_injective : Function.Injective toF := by
  have ht : Transcendental ℚ (muF : Fμ) := by
    intro halg

    have halg' : @IsAlgebraic ℚ Fμ _ _ (Fμ).algebra muF := by
      convert halg
      exact Subsingleton.elim _ _
    have h2 : IsAlgebraic ℚ ((muF : Fμ) : L) := IntermediateField.isAlgebraic_iff.mp halg'
    exact ModularCurve.transcendental_lambdaModC ℚ h2
  exact transcendental_iff_injective.mp ht

theorem algebraMap_comp_toF :
    (algebraMap Fμ L).comp toF = Polynomial.eval₂RingHom (algebraMap ℚ L) μ := by
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · simp [toF]
  · simp [toF]
    rfl

def ι : Polynomial (Polynomial ℚ) →+* Polynomial Fμ := Polynomial.mapRingHom toF

theorem ι_injective : Function.Injective ι := Polynomial.map_injective toF toF_injective

theorem aeval_ι (P : Polynomial (Polynomial ℚ)) (y : L) :
    Polynomial.aeval y (ι P) = ev2 P μ y := by
  rw [Polynomial.aeval_def, ι, coe_mapRingHom, eval₂_map, algebraMap_comp_toF]
  rfl

theorem minpoly_eq_ι (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    minpoly Fμ μq = ι (PsiQ q data) := by
  rw [ModularCurve.minpoly_lambdaNModC_eq ℚ q hq2 data, ι, coe_mapRingHom, PsiQ, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [toF, muF]

theorem psiQ_dvd_swap (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    PsiQ q data ∣ swap ℚ (PsiQ q data) := by

  have hF : ι (PsiQ q data) ∣ ι (swap ℚ (PsiQ q data)) := by
    rw [← minpoly_eq_ι q hq2 data]
    refine minpoly.dvd Fμ μq ?_
    rw [aeval_ι, ev2_swap_PsiQ q hq2 data]

  have hm := PsiQ_monic q data
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hm]
  apply ι_injective
  rw [map_zero, ι, coe_mapRingHom, Polynomial.map_modByMonic _ hm]
  exact (Polynomial.modByMonic_eq_zero_iff_dvd (hm.map _)).mpr hF

theorem natDegree_swap_le (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    (swap ℚ (PsiQ q data)).natDegree ≤ q + 1 := by
  obtain ⟨G, hG⟩ := psiQ_dvd_swap q hq2 data

  have h : PsiQ q data = swap ℚ (PsiQ q data) * swap ℚ G := by
    conv_lhs => rw [← swap_swap (PsiQ q data), hG, map_mul]
  have hne : PsiQ q data ≠ 0 := (PsiQ_monic q data).ne_zero
  have h1 : swap ℚ (PsiQ q data) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact hne h
  have h2 : swap ℚ G ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact hne h
  have hdeg := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_mul h1 h2, PsiQ_natDegree] at hdeg
  omega

theorem xdeg (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (k : ℕ) :
    (data.Ψ.coeff k).natDegree ≤ q + 1 := by
  have h1 : (data.Ψ.coeff k).natDegree = ((PsiQ q data).coeff k).natDegree := by
    rw [PsiQ, Polynomial.coeff_map, coe_mapRingHom,
      Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ))]
  rw [h1]
  exact (natDegree_coeff_le_natDegree_swap (PsiQ q data) k).trans (natDegree_swap_le q hq2 data)

end LambdaXdegSol
p2m_reactivate "P2MW.S_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le.LambdaXdegSol"

end
p2m_reactivate "P2MW.S_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le.LambdaXdegSol"

open ModularCurve in
theorem solution (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (k : ℕ) :
    (data.Ψ.coeff k).natDegree ≤ q + 1 :=
  LambdaXdegSol.xdeg q hq2 data k

end S_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le
end P2MW
export P2MW.S_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le (solution)
