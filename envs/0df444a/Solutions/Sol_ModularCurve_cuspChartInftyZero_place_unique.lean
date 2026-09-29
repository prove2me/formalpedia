-- Prove2me | solution 1 for ModularCurve.cuspChartInftyZero_place_unique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e63084d8-a8a9-5d46-b768-1915274cd647

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqNModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_le
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_AlgebraicCurve_Place_eq_of_finrank_lt_two_mul_ramificationIndex
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_weighted_support_le
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cuspChartInftyZero_place_unique
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open AlgebraicCurve ModularCurve

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve ModularCurve IntermediateField Polynomial

noncomputable section

namespace S09CDT

section OrdArith

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_add_eq_zero (w : Place K F) {u z : F} (hu0 : u ≠ 0) (hu : w.ord u = 0)
    (humem : u ∈ w.toValuationSubring) (hz : z ∈ w.toValuationSubring) (hzpos : z = 0 ∨ 0 < w.ord z) :
    u + z ≠ 0 ∧ w.ord (u + z) = 0 := by
  rcases hzpos with rfl | hzpos
  · simpa using ⟨hu0, hu⟩
  have hz0 : z ≠ 0 := by rintro rfl; simp at hzpos
  have hzmax : (⟨z, hz⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (w.mem_maximalIdeal_iff_ord_pos hz0 hz).mpr hzpos
  have humax : (⟨u, humem⟩ : w.toValuationSubring) ∉ IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [w.mem_maximalIdeal_iff_ord_pos hu0 humem]; omega
  have hsmem : u + z ∈ w.toValuationSubring := add_mem humem hz
  have hne : u + z ≠ 0 := by
    intro h
    apply humax
    have : (⟨u, humem⟩ : w.toValuationSubring) = -⟨z, hz⟩ :=
      Subtype.ext (eq_neg_of_add_eq_zero_left h)
    rw [this]; exact neg_mem hzmax
  refine ⟨hne, ?_⟩
  have hnonneg : 0 ≤ w.ord (u + z) := (w.mem_iff_ord_nonneg hne).mp hsmem
  by_contra hcon
  have hpos : 0 < w.ord (u + z) := lt_of_le_of_ne hnonneg (Ne.symm hcon)
  have hsmax : (⟨u + z, hsmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (w.mem_maximalIdeal_iff_ord_pos hne hsmem).mpr hpos
  apply humax
  have : (⟨u, humem⟩ : w.toValuationSubring) = ⟨u + z, hsmem⟩ - ⟨z, hz⟩ := Subtype.ext (by simp)
  rw [this]; exact sub_mem hsmax hzmax

theorem ord_eq_zero_of_ord_sub_one_pos (w : Place K F) {g : F} (hg : 0 < w.ord (g - 1)) : g ≠ 0 ∧ w.ord g = 0 := by
  have hz0 : g - 1 ≠ 0 := by rintro h; rw [h, Place.ord_zero] at hg; exact lt_irrefl _ hg
  have h := ord_add_eq_zero w one_ne_zero w.ord_one (one_mem _) ((w.mem_iff_ord_nonneg hz0).mpr hg.le) (Or.inr hg)
  rwa [add_sub_cancel] at h

theorem ord_pow (w : Place K F) {g : F} (hg : g ≠ 0) (n : ℕ) : w.ord (g ^ n) = n * w.ord g := by
  induction n with
  | zero => simp [Place.ord_one]
  | succ n ih => rw [pow_succ, w.ord_mul (pow_ne_zero _ hg) hg, ih]; push_cast; ring

theorem ord_div (w : Place K F) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : w.ord (a / b) = w.ord a - w.ord b := by
  rw [div_eq_mul_inv, w.ord_mul ha (inv_ne_zero hb), Place.ord_inv, sub_eq_add_neg]

end OrdArith

section Counting

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem place_eq_of_vanishing_chart {p : ℕ} (hp : 2 ≤ p) (hfin : Module.finrank F F' ≤ p + 1)
    {jF : F} (hpole : ∀ v v' : Place K F, v.ord jF < 0 → v'.ord jF < 0 → v = v')
    (hpole1 : ∀ v : Place K F, v.ord jF < 0 → v.ord jF = -1)
    (Φ : Polynomial (Polynomial ℤ))
    (hΦ₁ : ∀ b a : ℕ, ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → 1 * a + p * b ≤ p ^ 2 + p - 1)
    (hΦ₂ : ∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 → p * a + 1 * b ≤ p ^ 2 + p - 1)
    {y : F'} (hrel : Φ.eval₂ (eval₂RingHom (Int.castRingHom F') (algebraMap F F' (jF⁻¹)⁻¹)) y = 0)
    {U U' : Place K F'}
    (hUj : U.ord (algebraMap F F' jF) < 0) (hUt : 0 < U.ord (y * algebraMap F F' (jF⁻¹ ^ p)))
    (hU'j : U'.ord (algebraMap F F' jF) < 0) (hU't : 0 < U'.ord (y * algebraMap F F' (jF⁻¹ ^ p))) : U = U' := by
  have hj0 : jF ≠ 0 := by
    rintro rfl
    rw [map_zero, Place.ord_zero] at hUj
    exact lt_irrefl _ hUj
  have hjF' : algebraMap F F' jF ≠ 0 := (_root_.map_ne_zero _).mpr hj0
  rw [inv_inv] at hrel
  have key : ∀ W : Place K F', W.ord (algebraMap F F' jF) < 0 → 0 < W.ord (y * algebraMap F F' (jF⁻¹ ^ p)) →
      (W.restrict F).ord jF < 0 ∧ p ≤ W.ramificationIndex F := by
    intro W hWj hWt
    obtain ⟨hWy, hdich⟩ := Place.ord_eq_mul_or_eq_mul_of_modular_support W (by omega) Φ hΦ₁ hΦ₂ hrel hWj
    have hy0 : y ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hWy; exact lt_irrefl _ hWy

    have ht : W.ord (y * algebraMap F F' (jF⁻¹ ^ p)) = W.ord y - p * W.ord (algebraMap F F' jF) := by
      rw [map_pow, map_inv₀, W.ord_mul hy0 (pow_ne_zero _ (inv_ne_zero hjF')), ord_pow W (inv_ne_zero hjF'),
        Place.ord_inv]
      ring
    rw [ht] at hWt
    rcases hdich with hxy | hyx
    ·
      have hres := Place.ord_restrict (F := F) W jF
      have hvneg : (W.restrict F).ord jF < 0 := by
        by_contra hcon
        have : (0 : ℤ) ≤ (W.ramificationIndex F : ℤ) * (W.restrict F).ord jF := mul_nonneg (by positivity) (not_lt.mp hcon)
        omega
      refine ⟨hvneg, ?_⟩
      rw [hpole1 _ hvneg] at hres
      have : (p : ℤ) ≤ W.ramificationIndex F := by nlinarith
      exact_mod_cast this
    ·
      exfalso
      rw [hyx] at hWt
      simp at hWt
  obtain ⟨hUv, hUe⟩ := key U hUj hUt
  obtain ⟨hU'v, hU'e⟩ := key U' hU'j hU't
  exact Place.eq_of_finrank_lt_two_mul_ramificationIndex (hpole _ _ hU'v hUv) (by omega) hUe hU'e

end Counting

variable (K : Type*) [Field K]

abbrev Fj : IntermediateField K (LaurentSeries K) := adjoin K ({jqModC K} : Set (LaurentSeries K))

abbrev jF : Fj K := ⟨jqModC K, mem_adjoin_simple_self K _⟩

def psi : RatFunc K →ₐ[K] LaurentSeries K :=
  RatFunc.liftAlgHom (aeval (jqModC K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (transcendental_jqModC K)))

theorem psi_injective : Function.Injective (psi K) :=
  RatFunc.liftAlgHom_injective _ (transcendental_iff_injective.mp (transcendental_jqModC K))

theorem psi_mem (f : RatFunc K) : psi K f ∈ Fj K := by
  rw [← f.num_div_denom, psi, RatFunc.liftAlgHom_apply_div]
  exact (mem_adjoin_simple_iff K _).mpr ⟨_, _, rfl⟩

theorem psi_X : psi K RatFunc.X = jqModC K := by
  rw [psi, RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X]
  simp

def ratFuncEquiv : RatFunc K ≃+* Fj K :=
  RingEquiv.ofBijective
    ({ toFun := fun f => ⟨psi K f, psi_mem K f⟩
       map_one' := Subtype.ext (map_one (psi K))
       map_mul' := fun a b => Subtype.ext (map_mul (psi K) a b)
       map_zero' := Subtype.ext (map_zero (psi K))
       map_add' := fun a b => Subtype.ext (map_add (psi K) a b) } : RatFunc K →+* Fj K)
    ⟨fun a b hab => psi_injective K (congrArg Subtype.val hab), by
      rintro ⟨x, hx⟩
      obtain ⟨r, s, rfl⟩ := (mem_adjoin_simple_iff K _).mp hx
      refine ⟨algebraMap _ _ r / algebraMap _ _ s, Subtype.ext ?_⟩
      show psi K (algebraMap _ _ r / algebraMap _ _ s) = _
      rw [psi, RatFunc.liftAlgHom_apply_div]⟩

theorem ratFuncEquiv_algebraMap (a : K) :
    ratFuncEquiv K (algebraMap K (RatFunc K) a) = algebraMap K (Fj K) a :=
  Subtype.ext (by exact (psi K).commutes a)

theorem ratFuncEquiv_X : ratFuncEquiv K RatFunc.X = jF K := Subtype.ext (psi_X K)

theorem eq_congr_placeInfty_of_ord_jF_neg [DecidableEq (RatFunc K)] {w : Place K (Fj K)} (hw : w.ord (jF K) < 0) :
    w = Place.congrEquiv (ratFuncEquiv K) (ratFuncEquiv_algebraMap K) (RationalFunctionField.placeInfty K) := by
  obtain ⟨w₀, rfl⟩ := (Place.congrEquiv (ratFuncEquiv K) (ratFuncEquiv_algebraMap K)).surjective w
  congr 1
  apply RationalFunctionField.eq_placeInfty_of_ord_X_neg
  rwa [Place.congrEquiv_apply, ← ratFuncEquiv_X K, Place.ord_congrRingEquiv] at hw

theorem place_eq_of_ord_jF_neg {v v' : Place K (Fj K)} (hv : v.ord (jF K) < 0) (hv' : v'.ord (jF K) < 0) :
    v = v' := by
  classical
  rw [eq_congr_placeInfty_of_ord_jF_neg K hv, eq_congr_placeInfty_of_ord_jF_neg K hv']

theorem ord_jF_eq_neg_one {v : Place K (Fj K)} (hv : v.ord (jF K) < 0) : v.ord (jF K) = -1 := by
  classical
  rw [eq_congr_placeInfty_of_ord_jF_neg K hv, Place.congrEquiv_apply, ← ratFuncEquiv_X K, Place.ord_congrRingEquiv,
    ← RatFunc.algebraMap_X, RationalFunctionField.ord_placeInfty_algebraMap X_ne_zero, natDegree_X]
  rfl

variable (p : ℕ) [Fact p.Prime]

abbrev FjN : IntermediateField (Fj K) (LaurentSeries K) := adjoin (Fj K) ({jqNModC K p} : Set (LaurentSeries K))

abbrev jpFN : FjN K p := ⟨jqNModC K p, mem_adjoin_simple_self _ _⟩

theorem modularFunctionFieldC_eq_restrictScalars :
    modularFunctionFieldC K p = (FjN K p).restrictScalars K := by
  show modularFunctionFieldC K p =
    (adjoin (adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K p} : Set (LaurentSeries K))).restrictScalars K
  erw [adjoin_adjoin_left]
  rw [Set.singleton_union]
  rfl

def toFjN : modularFunctionFieldC K p ≃+* FjN K p :=
  (equivOfEq (modularFunctionFieldC_eq_restrictScalars K p)).toRingEquiv.trans
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

theorem toFjN_algebraMap (a : K) :
    toFjN K p (algebraMap K (modularFunctionFieldC K p) a) = algebraMap K (FjN K p) a :=
  Subtype.ext rfl

theorem toFjN_jC : toFjN K p ⟨jqModC K, jqModC_mem K p⟩ = algebraMap (Fj K) (FjN K p) (jF K) :=
  Subtype.ext rfl

theorem toFjN_jpC : toFjN K p ⟨jqNModC K p, jqNModC_mem K p⟩ = jpFN K p :=
  Subtype.ext rfl

theorem isSeparable_of_ne_zero (data : ModularPolynomialData p) (hsymm : EvalSymm data.Φ) (hpK : (p : K) ≠ 0) :
    Algebra.IsSeparable (Fj K) (FjN K p) :=
  (isSeparable_adjoin_simple_iff_isSeparable (Fj K) (LaurentSeries K)).mpr
    (isSeparable_jqNModC_of_modularPolynomialData K data hsymm hpK)

theorem isSeparable_of_eq_zero (hpK : (p : K) = 0) : Algebra.IsSeparable (Fj K) (FjN K p) := by
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpK
  have h : jqNModC K p = algebraMap (Fj K) (LaurentSeries K) (jF K ^ p) := by
    show jqNModC K p = ((jF K ^ p : Fj K) : LaurentSeries K)
    rw [jqNModC, qExpand_jqModC_eq_pow_unconditional K]
    rfl
  refine (isSeparable_adjoin_simple_iff_isSeparable (Fj K) (LaurentSeries K)).mpr ?_
  rw [h]
  exact isSeparable_algebraMap _

theorem isSeparable_FjN : Algebra.IsSeparable (Fj K) (FjN K p) := by
  by_cases hpK : (p : K) = 0
  · exact isSeparable_of_eq_zero K p hpK
  · obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm p
    exact isSeparable_of_ne_zero K p data hsymm hpK

section TChart

variable {K p}

theorem relation_FjN (data : ModularPolynomialData p) :
    data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (FjN K p)) (algebraMap (Fj K) (FjN K p) ((jF K)⁻¹)⁻¹)) (jpFN K p) = 0 := by
  have hrel := data.eval_jqNModC_mul_eq_zero K 1
  apply (algebraMap (FjN K p) (LaurentSeries K)).injective
  rw [map_zero, hom_eval₂]
  have h1 : (algebraMap (FjN K p) (LaurentSeries K)).comp
      (eval₂RingHom (Int.castRingHom (FjN K p)) (algebraMap (Fj K) (FjN K p) ((jF K)⁻¹)⁻¹))
      = (aeval (jqNModC K 1)).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, inv_inv, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_X, jqNModC_one]
      rfl
  have h2 : algebraMap (FjN K p) (LaurentSeries K) (jpFN K p) = jqNModC K (1 * p) := by
    show jqNModC K p = jqNModC K (1 * p)
    simp only [jqNModC]
    exact qExpand_congr (Nat.one_mul p).symm _
  rw [h1, h2]
  exact hrel

set_option synthInstance.maxHeartbeats 800000 in
theorem toFjN_tchart :
    toFjN K p (⟨jqNModC K p, jqNModC_mem K p⟩ * (⟨jqModC K, jqModC_mem K p⟩ : modularFunctionFieldC K p)⁻¹ ^ p)
      = jpFN K p * algebraMap (Fj K) (FjN K p) ((jF K)⁻¹ ^ p) := by
  rw [map_mul, map_pow, map_inv₀, toFjN_jC, toFjN_jpC, map_pow, map_inv₀]

end TChart

set_option synthInstance.maxHeartbeats 800000 in

theorem cuspChartInftyZero_place_unique :
    ∀ u u' : Place K (modularFunctionFieldC K p),
      u.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 →
      0 < u.ord (⟨jqNModC K p, jqNModC_mem K p⟩ * (⟨jqModC K, jqModC_mem K p⟩)⁻¹ ^ p) →
      u'.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 →
      0 < u'.ord (⟨jqNModC K p, jqNModC_mem K p⟩ * (⟨jqModC K, jqModC_mem K p⟩)⁻¹ ^ p) → u = u' := by
  intro u u' hu hut hu' hut'
  obtain ⟨data⟩ := nonempty_modularPolynomialData p
  haveI : FiniteDimensional (Fj K) (FjN K p) := finiteDimensional_adjoin_jqNModC K data
  haveI : Algebra.IsSeparable (Fj K) (FjN K p) := isSeparable_FjN K p
  have hfin : Module.finrank (Fj K) (FjN K p) ≤ p + 1 :=
    (finrank_adjoin_jqNModC_le K data).trans_eq (dedekindPsi_prime Fact.out)
  set e := toFjN K p with he_def
  have he := toFjN_algebraMap K p
  apply (Place.congrEquiv e he).injective
  simp only [Place.congrEquiv_apply]
  have hord : ∀ (w : Place K (modularFunctionFieldC K p)) (f : modularFunctionFieldC K p),
      (Place.congrRingEquiv e he w).ord (e f) = w.ord f := fun w f => Place.ord_congrRingEquiv e he w f
  have hUj : (Place.congrRingEquiv e he u).ord (algebraMap (Fj K) (FjN K p) (jF K)) < 0 := by
    rw [← toFjN_jC, hord]; exact hu
  have hU'j : (Place.congrRingEquiv e he u').ord (algebraMap (Fj K) (FjN K p) (jF K)) < 0 := by
    rw [← toFjN_jC, hord]; exact hu'
  have hUt : 0 < (Place.congrRingEquiv e he u).ord (jpFN K p * algebraMap (Fj K) (FjN K p) ((jF K)⁻¹ ^ p)) := by
    rw [← toFjN_tchart, hord]; exact hut
  have hU't : 0 < (Place.congrRingEquiv e he u').ord (jpFN K p * algebraMap (Fj K) (FjN K p) ((jF K)⁻¹ ^ p)) := by
    rw [← toFjN_tchart, hord]; exact hut'
  obtain ⟨hΦ₁, hΦ₂⟩ := data.weighted_support_le
  exact place_eq_of_vanishing_chart (Fact.out : p.Prime).two_le hfin (fun v v' hv hv' => place_eq_of_ord_jF_neg K hv hv')
    (fun v hv => ord_jF_eq_neg_one K hv) data.Φ hΦ₁ hΦ₂ (relation_FjN data) hUj hUt hU'j hU't

end S09CDT

end

open AlgebraicCurve ModularCurve in
theorem solution : ∀ (K : Type*) [Field K] (p : ℕ) [Fact p.Prime], ∀ u u' : Place K (modularFunctionFieldC K p), u.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 → 0 < u.ord (⟨jqNModC K p, jqNModC_mem K p⟩ * (⟨jqModC K, jqModC_mem K p⟩)⁻¹ ^ p) → u'.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 → 0 < u'.ord (⟨jqNModC K p, jqNModC_mem K p⟩ * (⟨jqModC K, jqModC_mem K p⟩)⁻¹ ^ p) → u = u' :=
  @S09CDT.cuspChartInftyZero_place_unique

end S_ModularCurve_cuspChartInftyZero_place_unique
end P2MW
export P2MW.S_ModularCurve_cuspChartInftyZero_place_unique (solution)
