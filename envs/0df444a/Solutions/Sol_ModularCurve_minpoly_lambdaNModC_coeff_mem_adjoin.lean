-- Prove2me | solution 1 for ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6807976e-58eb-5d0e-a588-bf0e4e899d9d

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LambdaSeries
import Theorems.Thm_ModularCurve_exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin
import Theorems.Thm_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg
import Theorems.Thm_ModularCurve_mem_adjoin_lambdaModC_of_pow_mul_mem
import Theorems.Thm_Polynomial_mem_range_aeval_of_isCoprime_of_pow_mul_eq
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Theorems.Thm_ModularCurve_exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub
import Theorems.Thm_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC
import Theorems.Thm_ModularCurve_lambdaModC_mem_modularFunctionFieldFull_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_mem_adjoin
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

open ModularCurve Polynomial

namespace LambdaDescentSol

section Supp

variable {R : Type*} [CommRing R]

def SuppGE (n : ℤ) (x : LaurentSeries R) : Prop := ∀ k < n, x.coeff k = 0

namespace SuppGE

variable {n a b : ℤ} {x y : LaurentSeries R}

theorem mono {m : ℤ} (h : m ≤ n) (hx : SuppGE n x) : SuppGE m x := fun k hk => hx k (lt_of_lt_of_le hk h)

theorem add (hx : SuppGE n x) (hy : SuppGE n y) : SuppGE n (x + y) :=
  fun k hk => by rw [HahnSeries.coeff_add, hx k hk, hy k hk, add_zero]

theorem neg (hx : SuppGE n x) : SuppGE n (-x) :=
  fun k hk => by rw [HahnSeries.coeff_neg, hx k hk, neg_zero]

theorem sub (hx : SuppGE n x) (hy : SuppGE n y) : SuppGE n (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem single' (m : ℤ) (r : R) : SuppGE m (HahnSeries.single m r) :=
  fun k hk => HahnSeries.coeff_single_of_ne (ne_of_lt hk)

theorem C' (r : R) : SuppGE 0 (HahnSeries.C r : LaurentSeries R) := single' 0 r

theorem one' : SuppGE 0 (1 : LaurentSeries R) := by
  have h := C' (1 : R)
  rwa [map_one] at h

theorem ofNat' (m : ℕ) [m.AtLeastTwo] : SuppGE 0 (OfNat.ofNat m : LaurentSeries R) := by
  have h := C' (R := R) (OfNat.ofNat m)
  rwa [map_ofNat] at h

theorem mul (hx : SuppGE a x) (hy : SuppGE b y) : SuppGE (a + b) (x * y) := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun ij hij => ?_)
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨h1, h2, h3⟩ := hij
  rw [HahnSeries.mem_support] at h1 h2
  have ha : a ≤ ij.1 := not_lt.mp (fun hlt => h1 (hx _ hlt))
  have hb : b ≤ ij.2 := not_lt.mp (fun hlt => h2 (hy _ hlt))
  omega

theorem pow (hx : SuppGE a x) : ∀ m : ℕ, SuppGE (m * a) (x ^ m)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_mul]; exact one'
  | m + 1 => by rw [pow_succ, Nat.cast_succ, add_mul, one_mul]; exact (pow hx m).mul hx

theorem pow0 (hx : SuppGE 0 x) (m : ℕ) : SuppGE 0 (x ^ m) := by simpa using hx.pow m

theorem qExpand' (hx : SuppGE a x) (N : ℕ) [NeZero N] : SuppGE (N * a) (ModularCurve.qExpand R N x) := by
  intro k hk
  by_cases hd : (N : ℤ) ∣ k
  · obtain ⟨k', rfl⟩ := hd
    rw [qExpand_coeff_mul]
    refine hx k' ?_
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact lt_of_mul_lt_mul_left hk hN.le
  · exact qExpand_coeff_of_not_dvd N x hd

theorem laurentMap' (hx : SuppGE a x) {S : Type*} [CommRing S] (f : R →+* S) :
    SuppGE a (ModularCurve.laurentMap f x) :=
  fun k hk => by rw [laurentMap_coeff, hx k hk, map_zero]

theorem ofPowerSeries' (p : PowerSeries R) : SuppGE 0 (HahnSeries.ofPowerSeries ℤ R p) :=
  fun k hk => ofPowerSeries_coeff_of_neg p hk

end SuppGE

theorem coeff_mul_of_suppGE {a b : ℤ} {x y : LaurentSeries R} (hx : SuppGE a x) (hy : SuppGE b y) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  rw [HahnSeries.coeff_mul, Finset.sum_eq_single (a, b)]
  · intro ij hij hne
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    rw [HahnSeries.mem_support] at h1 h2
    have ha : a ≤ ij.1 := not_lt.mp (fun hlt => h1 (hx _ hlt))
    have hb : b ≤ ij.2 := not_lt.mp (fun hlt => h2 (hy _ hlt))
    exfalso
    apply hne
    refine Prod.ext ?_ ?_
    · show ij.1 = a
      omega
    · show ij.2 = b
      omega
  · intro hn
    rw [Finset.mem_antidiagonal, not_and, not_and] at hn
    by_cases hxa : x.coeff a = 0
    · rw [hxa, zero_mul]
    by_cases hyb : y.coeff b = 0
    · rw [hyb, mul_zero]
    exact absurd rfl (hn (by rw [HahnSeries.mem_support]; exact hxa) (by rw [HahnSeries.mem_support]; exact hyb))

theorem coeff_pow_of_suppGE_zero {x : LaurentSeries R} (hx : SuppGE 0 x) :
    ∀ m : ℕ, (x ^ m).coeff 0 = (x.coeff 0) ^ m
  | 0 => by
      rw [pow_zero, pow_zero]
      have h : (HahnSeries.C (1 : R) : LaurentSeries R).coeff 0 = 1 := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
      rwa [map_one] at h
  | m + 1 => by
      rw [pow_succ, pow_succ, ← coeff_pow_of_suppGE_zero hx m]
      have h := coeff_mul_of_suppGE (hx.pow0 m) hx
      rwa [add_zero] at h

theorem coeff_C_zero (r : R) : (HahnSeries.C r : LaurentSeries R).coeff 0 = r := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem coeff_one_zero : (1 : LaurentSeries R).coeff 0 = 1 := by
  have h := coeff_C_zero (1 : R); rwa [map_one] at h

theorem coeff_ofNat_zero (m : ℕ) [m.AtLeastTwo] : (OfNat.ofNat m : LaurentSeries R).coeff 0 = (OfNat.ofNat m : R) := by
  have h := coeff_C_zero (R := R) (OfNat.ofNat m); rwa [map_ofNat] at h

theorem coeff_zero_of_suppGE_one {x : LaurentSeries R} (hx : SuppGE 1 x) : x.coeff 0 = 0 := hx 0 zero_lt_one

end Supp

theorem suppGE_lambdaInt_and_coeff : SuppGE 1 lambdaInt ∧ lambdaInt.coeff 1 = 1 := by

  set A : LaurentSeries ℤ := HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 with hA
  set X : LaurentSeries ℤ := qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) with hX
  set Y : LaurentSeries ℤ := qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) with hY
  have hdef : lambdaInt = HahnSeries.single 1 1 * (A * (X * Y)) := by
    rw [lambdaInt]; simp only [mul_assoc, hA, hX, hY]
  have hE : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ etaProd) := SuppGE.ofPowerSeries' _
  have hE0 : (HahnSeries.ofPowerSeries ℤ ℤ etaProd).coeff 0 = 1 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_etaProd]
  have hAs : SuppGE 0 A := hE.pow0 8
  have hA0 : A.coeff 0 = 1 := by rw [hA, coeff_pow_of_suppGE_zero hE, hE0, one_pow]
  have hXs : SuppGE 0 X := by rw [hX]; simpa using (hE.pow0 16).qExpand' 4
  have hX0 : X.coeff 0 = 1 := by
    have h := qExpand_coeff_mul 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) 0
    rw [mul_zero] at h
    rw [hX, h, coeff_pow_of_suppGE_zero hE, hE0, one_pow]
  have hD : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) := SuppGE.ofPowerSeries' _
  have hYs : SuppGE 0 Y := by rw [hY]; simpa using hD.qExpand' 2
  have hY0 : Y.coeff 0 = 1 := by
    have h := qExpand_coeff_mul 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) 0
    rw [mul_zero] at h
    rw [hY, h, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnitInv]
  have hZs : SuppGE 0 (A * (X * Y)) := by simpa using hAs.mul (hXs.mul hYs)
  have hZ0 : (A * (X * Y)).coeff 0 = 1 := by
    have h1 := coeff_mul_of_suppGE hXs hYs
    rw [add_zero] at h1
    have h2 := coeff_mul_of_suppGE hAs (hXs.mul hYs)
    simp only [add_zero] at h2
    rw [h2, h1, hA0, hX0, hY0]; ring
  refine ⟨?_, ?_⟩
  · rw [hdef]
    have h := (SuppGE.single' (R := ℤ) 1 1).mul hZs
    rwa [add_zero] at h
  · rw [hdef]
    have h := coeff_mul_of_suppGE (SuppGE.single' (R := ℤ) 1 1) hZs
    rw [add_zero] at h
    rw [h, HahnSeries.coeff_single_same, hZ0, one_mul]

theorem suppGE_mu : SuppGE 1 (lambdaModC ℚ) :=
  suppGE_lambdaInt_and_coeff.1.laurentMap' _

theorem coeff_mu_one : (lambdaModC ℚ).coeff 1 = 1 := by
  show (laurentMap (Int.castRingHom ℚ) lambdaInt).coeff 1 = 1
  rw [laurentMap_coeff, suppGE_lambdaInt_and_coeff.2, map_one]

theorem coeff_mu_zero : (lambdaModC ℚ).coeff 0 = 0 := suppGE_mu 0 zero_lt_one

theorem suppGE_one_sub : SuppGE 0 (1 - 16 * lambdaModC ℚ) :=
  SuppGE.one'.sub (((SuppGE.ofNat' 16).mul suppGE_mu).mono (by norm_num))

section Transport

variable (q : ℕ) [hq : Fact q.Prime]

local notation "L" => LaurentSeries ℚ
local notation "μ" => lambdaModC ℚ
local notation "C16" => (HahnSeries.C (1 / 16 : ℚ) : LaurentSeries ℚ)

theorem coeff_one_sub : (1 - 16 * μ).coeff 0 = 1 := by
  rw [sub_eq_add_neg, HahnSeries.coeff_add, HahnSeries.coeff_neg, coeff_one_zero]
  have h : SuppGE (0 + 1) (16 * μ) := (SuppGE.ofNat' 16).mul suppGE_mu
  rw [coeff_zero_of_suppGE_one (by simpa using h)]; ring

theorem one_sub_ne_zero : (1 : L) - 16 * μ ≠ 0 := by
  intro h
  have h' := congrArg (fun x : L => x.coeff 0) h
  rw [coeff_one_sub, HahnSeries.coeff_zero] at h'
  exact one_ne_zero h'

theorem C16_eq : C16 = algebraMap ℚ L (1 / 16 : ℚ) :=
  RingHom.congr_fun (Subsingleton.elim (HahnSeries.C : ℚ →+* L) (algebraMap ℚ L)) _

theorem sixteen_mul_C16 : (16 : L) * C16 = 1 := by
  rw [← map_ofNat (HahnSeries.C : ℚ →+* L) 16, ← map_mul]
  norm_num

theorem one_sub_C16 : (1 : L) - 16 * (C16 - μ) = 16 * μ := by
  rw [mul_sub, sixteen_mul_C16]; ring

abbrev Kμ : IntermediateField ℚ (LaurentSeries ℚ) := IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ))

abbrev FF : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull (4 * q)

theorem mu_mem_F : μ ∈ FF q :=
  full_degeneracy_le (dvd_mul_right 4 q) lambdaModC_mem_modularFunctionFieldFull_four

theorem muq_mem_F : lambdaNModC ℚ q ∈ FF q := by
  have h : qExpandₐ q μ ∈ (modularFunctionFieldFull 4).map (qExpandₐ q) :=
    (IntermediateField.mem_map _).mpr ⟨μ, lambdaModC_mem_modularFunctionFieldFull_four, rfl⟩
  exact full_degeneracy_map_le 4 q h

theorem K_le_F : Kμ ≤ FF q := IntermediateField.adjoin_simple_le_iff.mpr (mu_mem_F q)

theorem C16_mem_K : C16 ∈ Kμ := by rw [C16_eq]; exact Kμ.algebraMap_mem _

theorem sixteen_mem_K : (16 : L) ∈ Kμ := by
  have h := Kμ.algebraMap_mem (16 : ℚ)
  rwa [map_ofNat] at h

def muK : Kμ := ⟨lambdaModC ℚ, IntermediateField.mem_adjoin_simple_self ℚ (lambdaModC ℚ)⟩

def muF : FF q := ⟨lambdaModC ℚ, mu_mem_F q⟩
def muqF : FF q := ⟨lambdaNModC ℚ q, muq_mem_F q⟩

def ι : Kμ →+* FF q := (algebraMap Kμ L).codRestrict (FF q) (fun y => K_le_F q y.2)

theorem algebraMap_ι (y : Kμ) : algebraMap (FF q) L (ι q y) = (y : L) := by
  rw [IntermediateField.algebraMap_apply, ι, RingHom.codRestrict_apply, IntermediateField.algebraMap_apply]

theorem algebraMap_comp_ι : (algebraMap (FF q) L).comp (ι q) = algebraMap Kμ L := RingHom.ext (algebraMap_ι q)

theorem ι_muK : ι q muK = muF q := (algebraMap (FF q) L).injective rfl

theorem isIntegral_muq (hq2 : q ≠ 2) : IsIntegral Kμ (lambdaNModC ℚ q) := by
  have hfin := finrank_adjoin_lambdaModC_adjoin_lambdaNModC ℚ q hq2
  haveI : Module.Finite Kμ (IntermediateField.adjoin Kμ ({lambdaNModC ℚ q} : Set L)) :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact Nat.succ_pos q)
  have h : IsIntegral Kμ (⟨lambdaNModC ℚ q, IntermediateField.mem_adjoin_simple_self Kμ (lambdaNModC ℚ q)⟩ :
      IntermediateField.adjoin Kμ ({lambdaNModC ℚ q} : Set L)) :=
    IsIntegral.of_finite Kμ _
  exact IntermediateField.isIntegral_iff.mp h

theorem m_monic (hq2 : q ≠ 2) : (minpoly Kμ (lambdaNModC ℚ q)).Monic := minpoly.monic (isIntegral_muq q hq2)

theorem m_natDegree (hq2 : q ≠ 2) : (minpoly Kμ (lambdaNModC ℚ q)).natDegree = q + 1 := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_muq q hq2)]
  exact finrank_adjoin_lambdaModC_adjoin_lambdaNModC ℚ q hq2

variable (τ : ↥(modularFunctionFieldFull (4 * q)) →+* ↥(modularFunctionFieldFull (4 * q)))

def ψ : Kμ →+* L := ((algebraMap (FF q) L).comp τ).comp (ι q)

theorem ψ_apply (y : Kμ) : ψ q τ y = algebraMap (FF q) L (τ (ι q y)) := rfl

theorem ψ_muK (hτμ : algebraMap (FF q) L (τ (muF q)) = C16 - μ) : ψ q τ muK = C16 - μ := by
  rw [ψ_apply, ι_muK]; exact hτμ

theorem eval₂_ψ_minpoly (hτμq : algebraMap (FF q) L (τ (muqF q)) = C16 - lambdaNModC ℚ q) :
    (minpoly Kμ (lambdaNModC ℚ q)).eval₂ (ψ q τ) (C16 - lambdaNModC ℚ q) = 0 := by
  have h0 : algebraMap (FF q) L ((minpoly Kμ (lambdaNModC ℚ q)).eval₂ (ι q) (muqF q)) = 0 := by
    rw [hom_eval₂, algebraMap_comp_ι, ← aeval_def]
    exact minpoly.aeval Kμ _
  have h1 : (minpoly Kμ (lambdaNModC ℚ q)).eval₂ (ι q) (muqF q) = 0 :=
    (algebraMap (FF q) L).injective (by rw [h0, map_zero])
  have h2 := congrArg (fun y => algebraMap (FF q) L (τ y)) h1
  simp only [map_zero] at h2
  rw [hom_eval₂, hom_eval₂, hτμq] at h2
  exact h2

def msharp : Polynomial L := ((minpoly Kμ (lambdaNModC ℚ q)).map (ψ q τ)).comp (C C16 - X)

theorem lin_eq : (C C16 - X : Polynomial L) = -(X - C C16) := by ring

theorem natDegree_lin : (C C16 - X : Polynomial L).natDegree = 1 := by
  rw [lin_eq, natDegree_neg, natDegree_X_sub_C]

theorem leadingCoeff_lin : (C C16 - X : Polynomial L).leadingCoeff = -1 := by
  rw [lin_eq, leadingCoeff_neg, leadingCoeff_X_sub_C]

theorem lin_comp_lin : (C C16 - X : Polynomial L).comp (C C16 - X) = X := by
  rw [sub_comp, C_comp, X_comp]; ring

theorem msharp_eval (hτμq : algebraMap (FF q) L (τ (muqF q)) = C16 - lambdaNModC ℚ q) :
    (msharp q τ).eval (lambdaNModC ℚ q) = 0 := by
  rw [msharp, eval_comp, eval_sub, eval_C, eval_X, eval_map]
  exact eval₂_ψ_minpoly q τ hτμq

theorem msharp_monic (hq2 : q ≠ 2) : (msharp q τ).Monic := by
  have h1 := (m_monic q hq2).map (ψ q τ)
  rw [Monic, msharp, leadingCoeff_comp (by rw [natDegree_lin]; exact one_ne_zero), h1.leadingCoeff, leadingCoeff_lin,
    (m_monic q hq2).natDegree_map, m_natDegree q hq2, ((hq.out.odd_of_ne_two hq2).add_one).neg_one_pow, one_mul]

theorem msharp_natDegree (hq2 : q ≠ 2) : (msharp q τ).natDegree = q + 1 := by
  rw [msharp, natDegree_comp, natDegree_lin, (m_monic q hq2).natDegree_map, m_natDegree q hq2, mul_one]

theorem aeval_mem_K {x : L} (hx : x ∈ Kμ) (R : Polynomial ℚ) : aeval x R ∈ Kμ := by
  have h := (aeval (⟨x, (IntermediateField.mem_toSubalgebra _ _).mpr hx⟩ : Kμ.toSubalgebra) R).2
  rw [aeval_subalgebra_coe] at h
  exact (IntermediateField.mem_toSubalgebra _ _).mp h

theorem ψ_coeff_mem (hτμ : algebraMap (FF q) L (τ (muF q)) = C16 - μ)
    (h1 : ∀ i : ℕ, ∃ (b : ℕ) (R : Polynomial ℚ),
      (1 - 16 * μ) ^ b * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ R)
    (i : ℕ) : (ψ q τ) ((minpoly Kμ (lambdaNModC ℚ q)).coeff i) ∈ Kμ := by
  obtain ⟨b, R, hR⟩ := h1 i
  have hd : algebraMap Kμ L (1 - 16 * muK) = 1 - 16 * μ := by
    rw [map_sub, map_one, map_mul, map_ofNat]; rfl
  have hd0 : (1 - 16 * muK : Kμ) ≠ 0 := fun h => one_sub_ne_zero (by rw [← hd, h, map_zero])
  obtain ⟨φ⟩ : Nonempty (ℚ →+* Kμ) := ⟨algebraMap ℚ Kμ⟩

  have hy : (minpoly Kμ (lambdaNModC ℚ q)).coeff i = R.eval₂ φ muK * ((1 - 16 * muK) ^ b)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hd0)]
    apply (algebraMap Kμ L).injective
    rw [map_mul, map_pow, hd, hom_eval₂, Subsingleton.elim ((algebraMap Kμ L).comp φ) (algebraMap ℚ L), ← aeval_def,
      mul_comm]
    exact hR
  have hψd : (ψ q τ) (1 - 16 * muK) = 16 * μ := by
    rw [map_sub, map_one, map_mul, map_ofNat, ψ_muK q τ hτμ]; exact one_sub_C16
  rw [hy, map_mul, map_inv₀, map_pow, hom_eval₂, Subsingleton.elim ((ψ q τ).comp φ) (algebraMap ℚ L), ψ_muK q τ hτμ,
    ← aeval_def, hψd]
  exact mul_mem (aeval_mem_K (sub_mem C16_mem_K (IntermediateField.mem_adjoin_simple_self ℚ _)) R)
    (inv_mem (pow_mem (mul_mem sixteen_mem_K (IntermediateField.mem_adjoin_simple_self ℚ _)) b))

theorem msharp_eq (hq2 : q ≠ 2) (hτμ : algebraMap (FF q) L (τ (muF q)) = C16 - μ)
    (hτμq : algebraMap (FF q) L (τ (muqF q)) = C16 - lambdaNModC ℚ q)
    (h1 : ∀ i : ℕ, ∃ (b : ℕ) (R : Polynomial ℚ),
      (1 - 16 * μ) ^ b * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ R) :
    msharp q τ = (minpoly Kμ (lambdaNModC ℚ q)).map (algebraMap Kμ L) := by
  have hl : (minpoly Kμ (lambdaNModC ℚ q)).map (ψ q τ) ∈ Polynomial.lifts (algebraMap Kμ L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact ⟨⟨_, ψ_coeff_mem q τ hτμ h1 n⟩, rfl⟩
  obtain ⟨pK, hpK⟩ := (mem_lifts _).mp hl
  have hgK : (C (⟨C16, C16_mem_K⟩ : Kμ) - X : Polynomial Kμ).map (algebraMap Kμ L) = C C16 - X := by
    rw [Polynomial.map_sub, map_C, map_X]; rfl
  have hsh : (pK.comp (C (⟨C16, C16_mem_K⟩ : Kμ) - X)).map (algebraMap Kμ L) = msharp q τ := by
    rw [map_comp, hpK, hgK]; rfl
  have hdvd : minpoly Kμ (lambdaNModC ℚ q) ∣ pK.comp (C (⟨C16, C16_mem_K⟩ : Kμ) - X) :=
    minpoly.dvd Kμ _ (by rw [aeval_def, ← eval_map, hsh]; exact msharp_eval q τ hτμq)
  have hinj : Function.Injective (algebraMap Kμ L) := (algebraMap Kμ L).injective
  have hmon : (pK.comp (C (⟨C16, C16_mem_K⟩ : Kμ) - X)).Monic :=
    monic_of_injective hinj (by rw [hsh]; exact msharp_monic q τ hq2)
  have hdeg : (pK.comp (C (⟨C16, C16_mem_K⟩ : Kμ) - X)).natDegree = q + 1 := by
    rw [← natDegree_map_eq_of_injective hinj, hsh]; exact msharp_natDegree q τ hq2
  have heq := eq_of_monic_of_dvd_of_natDegree_le (m_monic q hq2) hmon hdvd (by rw [hdeg, m_natDegree q hq2])
  rw [← hsh, heq]

theorem map_ψ_eq_comp (hq2 : q ≠ 2) (hτμ : algebraMap (FF q) L (τ (muF q)) = C16 - μ)
    (hτμq : algebraMap (FF q) L (τ (muqF q)) = C16 - lambdaNModC ℚ q)
    (h1 : ∀ i : ℕ, ∃ (b : ℕ) (R : Polynomial ℚ),
      (1 - 16 * μ) ^ b * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ R) :
    (minpoly Kμ (lambdaNModC ℚ q)).map (ψ q τ) =
      ((minpoly Kμ (lambdaNModC ℚ q)).map (algebraMap Kμ L)).comp (C C16 - X) := by
  have h := msharp_eq q τ hq2 hτμ hτμq h1
  rw [msharp] at h
  rw [← h, comp_assoc, lin_comp_lin, comp_X]

theorem exists_common (hq2 : q ≠ 2)
    (h1 : ∀ i : ℕ, ∃ (b : ℕ) (R : Polynomial ℚ),
      (1 - 16 * μ) ^ b * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ R) :
    ∃ B : ℕ, ∀ i : ℕ, ∃ S : Polynomial ℚ,
      (1 - 16 * μ) ^ B * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ S := by
  classical
  choose b R hbR using h1
  refine ⟨∑ j ∈ Finset.range (q + 2), b j, fun i => ?_⟩
  by_cases hi : i < q + 2
  · have hle : b i ≤ ∑ j ∈ Finset.range (q + 2), b j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_range.mpr hi)
    refine ⟨(1 - 16 * X) ^ (∑ j ∈ Finset.range (q + 2), b j - b i) * R i, ?_⟩
    rw [map_mul, map_pow, map_sub, map_one, map_mul, map_ofNat, aeval_X, ← hbR i, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel hle]
  · refine ⟨0, ?_⟩
    have h0 : (minpoly Kμ (lambdaNModC ℚ q)).coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [m_natDegree q hq2]; omega)
    rw [h0]
    simp

theorem pow_mul_ψ_coeff (hq2 : q ≠ 2) (hτμ : algebraMap (FF q) L (τ (muF q)) = C16 - μ)
    (hτμq : algebraMap (FF q) L (τ (muqF q)) = C16 - lambdaNModC ℚ q)
    (h1 : ∀ i : ℕ, ∃ (b : ℕ) (R : Polynomial ℚ),
      (1 - 16 * μ) ^ b * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ R)
    (B : ℕ) (hB : ∀ i : ℕ, ∃ S : Polynomial ℚ,
      (1 - 16 * μ) ^ B * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ S) (k : ℕ) :
    ∃ S : Polynomial ℚ, (1 - 16 * μ) ^ B * (ψ q τ) ((minpoly Kμ (lambdaNModC ℚ q)).coeff k) = aeval μ S := by
  have hf : ∀ S : Polynomial ℚ, (aeval μ : Polynomial ℚ →ₐ[ℚ] L).toRingHom S = aeval μ S := fun S => rfl
  have hl : C ((1 - 16 * μ) ^ B) * (minpoly Kμ (lambdaNModC ℚ q)).map (algebraMap Kμ L) ∈
      Polynomial.lifts (aeval μ : Polynomial ℚ →ₐ[ℚ] L).toRingHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul, coeff_map]
    obtain ⟨S, hS⟩ := hB n
    exact ⟨S, by rw [hf]; exact hS.symm⟩
  obtain ⟨PA, hPA⟩ := (mem_lifts _).mp hl
  have hg : (C (C (1 / 16 : ℚ)) - X : Polynomial (Polynomial ℚ)).map (aeval μ : Polynomial ℚ →ₐ[ℚ] L).toRingHom
      = C C16 - X := by
    rw [Polynomial.map_sub, map_C, map_X, hf, aeval_C, ← C16_eq]
  have key : C ((1 - 16 * μ) ^ B) * (minpoly Kμ (lambdaNModC ℚ q)).map (ψ q τ)
      = (PA.comp (C (C (1 / 16 : ℚ)) - X)).map (aeval μ : Polynomial ℚ →ₐ[ℚ] L).toRingHom := by
    rw [map_comp, hPA, hg, mul_comp, C_comp, ← map_ψ_eq_comp q τ hq2 hτμ hτμq h1]
  refine ⟨(PA.comp (C (C (1 / 16 : ℚ)) - X)).coeff k, ?_⟩
  have hk := congrArg (fun p => Polynomial.coeff p k) key
  simp only [coeff_C_mul, coeff_map] at hk
  rw [hk, hf]

theorem tau_aeval (hτμ : algebraMap (FF q) L (τ (muF q)) = C16 - μ) (w : FF q) (p : Polynomial ℚ)
    (hw : algebraMap (FF q) L w = aeval μ p) : algebraMap (FF q) L (τ w) = aeval (C16 - μ) p := by
  obtain ⟨φ0⟩ : Nonempty (ℚ →+* FF q) := ⟨algebraMap ℚ (FF q)⟩
  have hw' : w = p.eval₂ φ0 (muF q) := (algebraMap (FF q) L).injective (by
    rw [hw, hom_eval₂, Subsingleton.elim ((algebraMap (FF q) L).comp φ0) (algebraMap ℚ L), aeval_def]; rfl)
  rw [hw', hom_eval₂, hom_eval₂, Subsingleton.elim ((algebraMap (FF q) L).comp (τ.comp φ0)) (algebraMap ℚ L), hτμ,
    ← aeval_def]

theorem transport (hq2 : q ≠ 2) (hττ : ∀ x, τ (τ x) = x) (hτμ : algebraMap (FF q) L (τ (muF q)) = C16 - μ)
    (hτμq : algebraMap (FF q) L (τ (muqF q)) = C16 - lambdaNModC ℚ q)
    (h1 : ∀ i : ℕ, ∃ (b : ℕ) (R : Polynomial ℚ),
      (1 - 16 * μ) ^ b * (((minpoly Kμ (lambdaNModC ℚ q)).coeff i : Kμ) : L) = aeval μ R)
    (k : ℕ) : ∃ (a : ℕ) (R : Polynomial ℚ),
      μ ^ a * (((minpoly Kμ (lambdaNModC ℚ q)).coeff k : Kμ) : L) = aeval μ R := by
  obtain ⟨B, hB⟩ := exists_common q hq2 h1
  obtain ⟨S, hS⟩ := pow_mul_ψ_coeff q τ hq2 hτμ hτμq h1 B hB k
  have hw : algebraMap (FF q) L ((1 - 16 * muF q) ^ B * τ (ι q ((minpoly Kμ (lambdaNModC ℚ q)).coeff k)))
      = aeval μ S := by
    rw [← hS, map_mul, map_pow, map_sub, map_one, map_mul, map_ofNat]; rfl
  have hT := tau_aeval q τ hτμ _ S hw
  simp only [map_mul, map_pow, map_sub, map_one, map_ofNat, hττ] at hT
  rw [hτμ, algebraMap_ι, one_sub_C16, mul_pow, mul_assoc] at hT

  refine ⟨B, C ((1 / 16 : ℚ) ^ B) * S.comp (C (1 / 16 : ℚ) - X), ?_⟩
  rw [map_mul, aeval_C, aeval_comp, map_sub, aeval_C, aeval_X, ← C16_eq, ← hT, map_pow, ← C16_eq, ← mul_assoc,
    ← mul_pow, mul_comm C16 (16 : L), sixteen_mul_C16, one_pow, one_mul]

end Transport

end LambdaDescentSol

theorem LambdaW4Transport.exists_pow_lambda_mul_coeff_eq (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (h1 : ∀ i : ℕ, ∃ (b : ℕ) (R : Polynomial ℚ),
      (1 - 16 * ModularCurve.lambdaModC ℚ) ^ b *
        (((minpoly (↥(IntermediateField.adjoin ℚ ({ModularCurve.lambdaModC ℚ} : Set (LaurentSeries ℚ))))
            (ModularCurve.lambdaNModC ℚ q)).coeff i
          : ↥(IntermediateField.adjoin ℚ ({ModularCurve.lambdaModC ℚ} : Set (LaurentSeries ℚ)))) : LaurentSeries ℚ)
      = Polynomial.aeval (ModularCurve.lambdaModC ℚ) R)
    (k : ℕ) :
    ∃ (a : ℕ) (R : Polynomial ℚ),
      ModularCurve.lambdaModC ℚ ^ a *
        (((minpoly (↥(IntermediateField.adjoin ℚ ({ModularCurve.lambdaModC ℚ} : Set (LaurentSeries ℚ))))
            (ModularCurve.lambdaNModC ℚ q)).coeff k
          : ↥(IntermediateField.adjoin ℚ ({ModularCurve.lambdaModC ℚ} : Set (LaurentSeries ℚ)))) : LaurentSeries ℚ)
      = Polynomial.aeval (ModularCurve.lambdaModC ℚ) R := by
  obtain ⟨τ, hττ, hτμ, hτμq⟩ := ModularCurve.exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub q hq2
  exact LambdaDescentSol.transport q (τ : ↥(ModularCurve.modularFunctionFieldFull (4 * q)) →+*
      ↥(ModularCurve.modularFunctionFieldFull (4 * q))) hq2 (fun x => hττ x)
    (hτμ (LambdaDescentSol.muF q) rfl) (hτμq (LambdaDescentSol.muqF q) rfl) h1 k

namespace LambdaDescentSol

section Main

variable (q : ℕ) [hq : Fact q.Prime]

local notation "L" => LaurentSeries ℚ
local notation "μ" => lambdaModC ℚ

def c (k : ℕ) : LaurentSeries ℚ := (((minpoly Kμ (lambdaNModC ℚ q)).coeff k : Kμ) : LaurentSeries ℚ)

theorem pow_mul_c_mem_A (hq2 : q ≠ 2) (k : ℕ) : ∃ N : ℕ, (1 - 16 * μ) ^ (4 * N) * c q k ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin q k
  refine ⟨N, mem_adjoin_lambdaModC_of_pow_mul_mem _ (fun n hn => ?_) N ?_⟩
  ·
    have h1 : SuppGE 0 ((1 - 16 * μ) ^ (4 * N)) := suppGE_one_sub.pow0 _
    have h2 : SuppGE 0 (c q k) := fun m hm => minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg q hq2 k m hm
    have h := h1.mul h2
    rw [add_zero] at h
    exact h n hn
  · have h : μ ^ N * ((1 - 16 * μ) ^ (4 * N) * c q k) = (μ * (1 - 16 * μ) ^ 4) ^ N * c q k := by
      rw [mul_pow, ← pow_mul, mul_assoc]
    rw [h]
    exact hN

theorem step1 (hq2 : q ≠ 2) (i : ℕ) : ∃ (b : ℕ) (R : Polynomial ℚ), (1 - 16 * μ) ^ b * c q i = aeval μ R := by
  obtain ⟨N, hN⟩ := pow_mul_c_mem_A q hq2 i
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hN
  obtain ⟨R, hR⟩ := hN
  exact ⟨4 * N, R, hR.symm⟩

theorem descent (hq2 : q ≠ 2) (k : ℕ) : c q k ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)) := by

  obtain ⟨a, P, hP⟩ := LambdaW4Transport.exists_pow_lambda_mul_coeff_eq q hq2 (step1 q hq2) k

  obtain ⟨b, Q, hQ⟩ := step1 q hq2 k

  rw [Algebra.adjoin_singleton_eq_range_aeval]
  have hcop : IsCoprime (X : Polynomial ℚ) (1 - 16 * X) := ⟨16, 1, by ring⟩
  refine Polynomial.mem_range_aeval_of_isCoprime_of_pow_mul_eq μ (transcendental_lambdaModC ℚ) hcop (c q k) a b P Q ?_ ?_
  · rw [aeval_X]
    exact hP
  · have h : aeval μ (1 - 16 * X : Polynomial ℚ) = 1 - 16 * μ := by
      rw [map_sub, map_one, map_mul, map_ofNat, aeval_X]
    rw [h]
    exact hQ

end Main

end LambdaDescentSol

end

open ModularCurve in
theorem solution (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (k : ℕ) :
    (((minpoly (↥(IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)))) (lambdaNModC ℚ q)).coeff k
        : LaurentSeries ℚ)) ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)) :=
  LambdaDescentSol.descent q hq2 k

end S_ModularCurve_minpoly_lambdaNModC_coeff_mem_adjoin
end P2MW
export P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_mem_adjoin (solution)
