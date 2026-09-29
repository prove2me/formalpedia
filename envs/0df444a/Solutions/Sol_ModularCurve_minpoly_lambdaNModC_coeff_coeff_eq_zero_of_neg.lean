-- Prove2me | solution 1 for ModularCurve.minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7b522829-217e-5e96-b764-8a6eadd18488

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC
import Theorems.Thm_ModularCurve_exists_algEquiv_full_four_mul_restrict_eq_qExpand
import Theorems.Thm_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
import Theorems.Thm_ModularCurve_lambdaModC_mem_modularFunctionFieldFull_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve ModularCurve.PhiGen Polynomial

namespace LambdaPsiQIntSol

abbrev Kμ : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ))

section Core

variable (q : ℕ) [hq : Fact q.Prime]

def P : Polynomial (LaurentSeries ℚ) :=
  (minpoly Kμ (lambdaNModC ℚ q)).map (algebraMap Kμ (LaurentSeries ℚ))

theorem coeff_P (k : ℕ) :
    (P q).coeff k = ((minpoly Kμ (lambdaNModC ℚ q)).coeff k : LaurentSeries ℚ) := by
  rw [P, coeff_map]; rfl

private theorem _root_.LambdaPsiQIntSol.isIntegral (hq2 : q ≠ 2) : IsIntegral Kμ (lambdaNModC ℚ q) := by
  have hfin := finrank_adjoin_lambdaModC_adjoin_lambdaNModC ℚ q hq2
  haveI : FiniteDimensional Kμ (IntermediateField.adjoin Kμ ({lambdaNModC ℚ q} : Set (LaurentSeries ℚ))) :=
    Module.finite_of_finrank_pos (by rw [hfin]; omega)
  have h := Algebra.IsIntegral.isIntegral (R := Kμ)
    (IntermediateField.AdjoinSimple.gen Kμ (lambdaNModC ℚ q))
  exact IntermediateField.isIntegral_iff.mp h

p2m_export "LambdaPsiQIntSol" "isIntegral"
theorem P_monic (hq2 : q ≠ 2) : (P q).Monic := (minpoly.monic (isIntegral q hq2)).map _

theorem P_natDegree (hq2 : q ≠ 2) : (P q).natDegree = q + 1 := by
  rw [P, (minpoly.monic (isIntegral q hq2)).natDegree_map,
    ← IntermediateField.adjoin.finrank (isIntegral q hq2)]
  exact finrank_adjoin_lambdaModC_adjoin_lambdaNModC ℚ q hq2

theorem P_eval : (P q).eval (lambdaNModC ℚ q) = 0 := by
  rw [P, eval_map, ← aeval_def]; exact minpoly.aeval _ _

scoped instance instNeZeroFour : NeZero (4 : ℕ) := ⟨by norm_num⟩

abbrev F : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull (4 * q)

theorem full4_le : modularFunctionFieldFull 4 ≤ F q := full_degeneracy_le (dvd_mul_right 4 q)

theorem Kμ_le_full4 : Kμ ≤ modularFunctionFieldFull 4 :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr lambdaModC_mem_modularFunctionFieldFull_four)

theorem Kμ_le : Kμ ≤ F q := Kμ_le_full4.trans (full4_le q)

theorem P_map_qExpand_eval (hq2 : q ≠ 2) : ((P q).map (qExpand ℚ q)).eval (lambdaModC ℚ) = 0 := by
  obtain ⟨σ, hσ, hσσ⟩ := exists_algEquiv_full_four_mul_restrict_eq_qExpand q hq2

  set ι : F q →+* LaurentSeries ℚ := algebraMap (F q) (LaurentSeries ℚ) with hι
  have hιapp : ∀ x : F q, ι x = (x : LaurentSeries ℚ) := fun x => rfl
  have hιinj : Function.Injective ι := Subtype.val_injective
  set μ' : F q := ⟨lambdaModC ℚ, full4_le q lambdaModC_mem_modularFunctionFieldFull_four⟩ with hμ'
  have hσμ : ι (σ μ') = lambdaNModC ℚ q := by
    rw [hιapp, hσ μ' lambdaModC_mem_modularFunctionFieldFull_four]; rfl
  have hσσμ : σ (σ μ') = μ' := hσσ μ'

  let incl : Kμ →+* F q :=
    { toFun := fun x => ⟨(x : LaurentSeries ℚ), Kμ_le q x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hincl : ∀ x : Kμ, ((incl x : F q) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := fun _ => rfl
  set m' : Polynomial (F q) := (minpoly Kμ (lambdaNModC ℚ q)).map incl with hm'
  have hm'P : m'.map ι = P q := by
    rw [hm', Polynomial.map_map, P]
    congr 1

  have h1 : m'.eval (σ μ') = 0 := by
    apply hιinj
    rw [map_zero, ← eval₂_hom, hσμ, ← eval_map, hm'P]
    exact P_eval q

  have h2 : (m'.map (σ : F q →+* F q)).eval μ' = 0 := by
    rw [eval_map, ← hσσμ, show σ (σ μ') = (σ : F q →+* F q) (σ μ') from rfl, eval₂_hom, h1, map_zero]

  have h3 : (m'.map (σ : F q →+* F q)).map ι = (P q).map (qExpand ℚ q) := by
    refine Polynomial.ext fun k => ?_
    simp only [coeff_map, hm']
    rw [coeff_P]
    exact hσ (incl ((minpoly Kμ (lambdaNModC ℚ q)).coeff k)) (Kμ_le_full4 ((minpoly Kμ (lambdaNModC ℚ q)).coeff k).2)
  have h4 := congrArg ι h2
  rwa [map_zero, ← eval₂_hom, ← eval_map, h3] at h4

theorem exists_isPrimitiveRoot_cyclotomicField (N : ℕ) [NeZero N] :
    ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z N := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ) (Set.mem_singleton N) (NeZero.ne N)

def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  ((exists_isPrimitiveRoot_cyclotomicField N).choose_spec.isUnit (NeZero.ne N)).unit

theorem cycUnit_spec (N : ℕ) [NeZero N] :
    IsPrimitiveRoot ((cycUnit N : (CyclotomicField N ℚ)ˣ) : CyclotomicField N ℚ) N := by
  rw [cycUnit, IsUnit.unit_spec]
  exact (exists_isPrimitiveRoot_cyclotomicField N).choose_spec

theorem cycUnit_pow (N : ℕ) [NeZero N] : cycUnit N ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, (cycUnit_spec N).pow_eq_one, Units.val_one])

abbrev Kc : Type := CyclotomicField q ℚ

def lconj {K : Type*} [Field K] (ζ : Kˣ) : Fin (q + 1) → LaurentSeries K :=
  Fin.cons (qExpand K (q * q) (lambdaModC K)) (fun b : Fin q => qTwist (ζ ^ (b : ℕ)) (lambdaModC K))

theorem lconj_zero {K : Type*} [Field K] (ζ : Kˣ) : lconj q ζ 0 = qExpand K (q * q) (lambdaModC K) := by
  simp [lconj]

theorem lconj_succ {K : Type*} [Field K] (ζ : Kˣ) (b : Fin q) :
    lconj q ζ b.succ = qTwist (ζ ^ (b : ℕ)) (lambdaModC K) := by
  simp [lconj]

theorem coeffEmb_qExpand_coeff (hq2 : q ≠ 2) (k : ℕ) :
    coeffEmb (Kc q) (qExpand ℚ q (((minpoly Kμ (lambdaNModC ℚ q)).coeff k : LaurentSeries ℚ))) =
      (phiProd q (lconj q (cycUnit q))).coeff k := by
  have h := map_eq_phiProd_lambda_of_eval_qExpand_eq_zero q (cycUnit q) (cycUnit_spec q) (P q)
    (P_monic q hq2) (P_natDegree q hq2) (P_eval q) (P_map_qExpand_eval q hq2)
  have hk := congrArg (fun R => Polynomial.coeff R k) h
  simp only [coeff_map, RingHom.comp_apply, coeff_P] at hk
  exact hk

end Core

end LambdaPsiQIntSol
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

end
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

noncomputable section

open ModularCurve ModularCurve.PhiGen Polynomial

namespace LambdaPsiQIntSol

section Supp

variable {R : Type*} [CommRing R]

def SuppGE (n : ℤ) (x : LaurentSeries R) : Prop := ∀ k < n, x.coeff k = 0

namespace SuppGE

variable {n a b : ℤ} {x y : LaurentSeries R}

theorem mono {m : ℤ} (h : m ≤ n) (hx : SuppGE n x) : SuppGE m x := fun k hk => hx k (lt_of_lt_of_le hk h)

theorem zero' (m : ℤ) : SuppGE m (0 : LaurentSeries R) := fun k _ => by rw [HahnSeries.coeff_zero]

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

theorem mul0 (hx : SuppGE 0 x) (hy : SuppGE 0 y) : SuppGE 0 (x * y) := by
  simpa using hx.mul hy

theorem pow (hx : SuppGE a x) : ∀ m : ℕ, SuppGE (m * a) (x ^ m)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_mul]; exact one'
  | m + 1 => by rw [pow_succ, Nat.cast_succ, add_mul, one_mul]; exact (pow hx m).mul hx

theorem pow0 (hx : SuppGE 0 x) (m : ℕ) : SuppGE 0 (x ^ m) := by simpa using hx.pow m

theorem sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries R) (h : ∀ i ∈ s, SuppGE n (f i)) :
    SuppGE n (∑ i ∈ s, f i) := by
  intro k hk
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi k hk

theorem qExpand' (hx : SuppGE a x) (N : ℕ) [NeZero N] : SuppGE (N * a) (ModularCurve.qExpand R N x) := by
  intro k hk
  by_cases hd : (N : ℤ) ∣ k
  · obtain ⟨k', rfl⟩ := hd
    rw [qExpand_coeff_mul]
    refine hx k' ?_
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact lt_of_mul_lt_mul_left hk hN.le
  · exact qExpand_coeff_of_not_dvd N x hd

theorem qExpand0 (hx : SuppGE 0 x) (N : ℕ) [NeZero N] : SuppGE 0 (ModularCurve.qExpand R N x) := by
  simpa using hx.qExpand' N

theorem qTwist' (hx : SuppGE a x) (u : Rˣ) : SuppGE a (ModularCurve.qTwist u x) :=
  fun k hk => by rw [qTwist_coeff, hx k hk, mul_zero]

theorem laurentMap' (hx : SuppGE a x) {S : Type*} [CommRing S] (f : R →+* S) :
    SuppGE a (ModularCurve.laurentMap f x) :=
  fun k hk => by rw [laurentMap_coeff, hx k hk, map_zero]

theorem ofPowerSeries' (p : PowerSeries R) : SuppGE 0 (HahnSeries.ofPowerSeries ℤ R p) :=
  fun k hk => ofPowerSeries_coeff_of_neg p hk

end SuppGE
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

end Supp
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

theorem suppGE_one_lambdaInt : SuppGE 1 lambdaInt := by
  have hE : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ etaProd) := SuppGE.ofPowerSeries' _
  have hD : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) := SuppGE.ofPowerSeries' _
  have h := (((SuppGE.single' (R := ℤ) 1 1).mul (hE.pow0 8)).mul ((hE.pow0 16).qExpand0 4)).mul (hD.qExpand0 2)
  simp only [add_zero] at h
  exact h

section PolySupp

variable {K : Type*} [Field K]

def CoeffsSuppGE (p : Polynomial (LaurentSeries K)) : Prop := ∀ k : ℕ, SuppGE 0 (p.coeff k)

theorem coeffsSuppGE_one : CoeffsSuppGE (1 : Polynomial (LaurentSeries K)) := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs
  · exact SuppGE.one'
  · exact SuppGE.zero' 0

theorem coeffsSuppGE_X_sub_C {a : LaurentSeries K} (ha : SuppGE 0 a) :
    CoeffsSuppGE (Polynomial.X - Polynomial.C a) := by
  intro k
  rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  refine SuppGE.sub ?_ ?_
  · split_ifs
    · exact SuppGE.one'
    · exact SuppGE.zero' 0
  · split_ifs
    · exact ha
    · exact SuppGE.zero' 0

theorem coeffsSuppGE_mul {p r : Polynomial (LaurentSeries K)} (hp : CoeffsSuppGE p) (hr : CoeffsSuppGE r) :
    CoeffsSuppGE (p * r) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact SuppGE.sum _ _ fun ij _ => (hp ij.1).mul0 (hr ij.2)

theorem coeffsSuppGE_prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial (LaurentSeries K))
    (hp : ∀ i ∈ s, CoeffsSuppGE (p i)) : CoeffsSuppGE (∏ i ∈ s, p i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using coeffsSuppGE_one
  | cons a s _ha ih =>
    rw [Finset.prod_cons]
    exact coeffsSuppGE_mul (hp a (Finset.mem_cons_self a s)) (ih fun i hi => hp i (Finset.mem_cons_of_mem hi))

end PolySupp
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

section ConjSupp

variable (q : ℕ) [hq : Fact q.Prime] {K : Type*} [Field K]

theorem suppGE_lambdaModC : SuppGE 0 (lambdaModC K) :=
  (suppGE_one_lambdaInt.mono (by norm_num)).laurentMap' _

theorem suppGE_lconj (ζ : Kˣ) (i : Fin (q + 1)) : SuppGE 0 (lconj q ζ i) := by
  induction i using Fin.cases with
  | zero => rw [lconj_zero]; exact (suppGE_lambdaModC (K := K)).qExpand0 _
  | succ b => rw [lconj_succ]; exact (suppGE_lambdaModC (K := K)).qTwist' _

theorem suppGE_phiProd_coeff (ζ : Kˣ) (k : ℕ) : SuppGE 0 ((phiProd q (lconj q ζ)).coeff k) := by
  rw [phiProd]
  exact coeffsSuppGE_prod Finset.univ _ (fun i _ => coeffsSuppGE_X_sub_C (suppGE_lconj q ζ i)) k

end ConjSupp
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

theorem qint (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) (k : ℕ) (n : ℤ) (hn : n < 0) :
    (((minpoly Kμ (lambdaNModC ℚ q)).coeff k : LaurentSeries ℚ)).coeff n = 0 := by
  have h1 : algebraMap ℚ (Kc q) ((((minpoly Kμ (lambdaNModC ℚ q)).coeff k : LaurentSeries ℚ)).coeff n)
      = ((phiProd q (lconj q (cycUnit q))).coeff k).coeff ((q : ℤ) * n) := by
    rw [← coeffEmb_qExpand_coeff q hq2 k, coeffEmb_coeff, qExpand_coeff_mul]
  have hqn : (q : ℤ) * n < 0 := by
    have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.out.pos
    exact Int.mul_neg_of_pos_of_neg hq0 hn
  rw [suppGE_phiProd_coeff q (cycUnit q) k _ hqn] at h1
  exact (algebraMap ℚ (Kc q)).injective (by rw [h1, map_zero])

end LambdaPsiQIntSol
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

end
p2m_reactivate "P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg.LambdaPsiQIntSol"

open ModularCurve in
theorem solution (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (k : ℕ) (n : ℤ) (hn : n < 0) :
    (((minpoly (↥(IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)))) (lambdaNModC ℚ q)).coeff k
        : LaurentSeries ℚ)).coeff n = 0 :=
  LambdaPsiQIntSol.qint q hq2 k n hn

#print axioms solution

end S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg
end P2MW
export P2MW.S_ModularCurve_minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg (solution)
