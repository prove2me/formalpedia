-- Prove2me | solution 1 for ModularCurve.cuspChartZeroInfty_place_unique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/25077466-0b4c-59d7-be07-3f14ccb45fc3

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_of_ord_X_neg
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_AlgebraicCurve_Place_eq_of_finrank_lt_two_mul_ramificationIndex
import Theorems.Thm_ModularCurve_ModularPolynomialData_weighted_support_le
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_mul_or_eq_mul_of_modular_support
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cuspChartZeroInfty_place_unique
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective IntermediateField Polynomial"

namespace P2MWs12
namespace CuspTwin

section eval
variable {A B : Type*} [CommRing A] [CommRing B]

def ev (Φ : Polynomial (Polynomial ℤ)) (x y : A) : A := Φ.eval₂ (eval₂RingHom (Int.castRingHom A) x) y

theorem aeval_toRingHom_eq [Algebra ℤ A] (x : A) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = eval₂RingHom (Int.castRingHom A) x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

theorem ev_eq_evalEval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = (Φ.map (mapRingHom (Int.castRingHom A))).evalEval x y := by
  rw [ev, ← eval₂_eval₂RingHom_apply]

theorem map_ev (φ : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    φ (ev Φ x y) = ev Φ (φ x) (φ y) := by
  rw [ev_eq_evalEval, ev_eq_evalEval, ← map_mapRingHom_evalEval φ, Polynomial.map_map, mapRingHom_comp,
    RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

theorem ev_eq_aevalAeval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = aevalAeval x y Φ := by
  have h : eval₂RingHom (eval₂RingHom (Int.castRingHom A) x) y = (aevalAeval (R := ℤ) x y).toRingHom := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp
    · simp
  exact RingHom.congr_fun h Φ

theorem ev_swap (Φ : Polynomial (Polynomial ℤ)) (x y : A) : ev (Bivariate.swap Φ) x y = ev Φ y x := by
  rw [ev_eq_aevalAeval, ev_eq_aevalAeval, Bivariate.aevalAeval_swap]

theorem ev_int (Φ : Polynomial (Polynomial ℤ)) (a b : ℤ) : ev Φ a b = Φ.evalEval a b := by
  rw [ev_eq_evalEval]
  congr 1
  have h : mapRingHom (Int.castRingHom ℤ) = RingHom.id (Polynomial ℤ) := by
    rw [RingHom.ext_int (Int.castRingHom ℤ) (RingHom.id ℤ)]; exact mapRingHom_id
  rw [h]; exact Polynomial.map_id

theorem ev_sub (Φ Ψ : Polynomial (Polynomial ℤ)) (x y : A) : ev (Φ - Ψ) x y = ev Φ x y - ev Ψ x y := by
  rw [ev_eq_aevalAeval, map_sub, ← ev_eq_aevalAeval, ← ev_eq_aevalAeval]

end eval

theorem swap_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) : Bivariate.swap Φ = Φ := by
  set G : Polynomial (Polynomial ℤ) := Bivariate.swap Φ - Φ with hG

  have hL : ∀ x y : LaurentSeries ℚ, ev G x y = 0 := fun x y => by
    have hxy := h x y
    rw [aeval_toRingHom_eq, aeval_toRingHom_eq] at hxy
    rw [hG, ev_sub, ev_swap, sub_eq_zero]; exact hxy.symm
  let ι : ℤ →+* LaurentSeries ℚ := (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ)
  have hι : Function.Injective ι := (algebraMap ℚ (LaurentSeries ℚ)).injective.comp Int.cast_injective
  have hZ : ∀ a b : ℤ, G.evalEval a b = 0 := fun a b => hι (by rw [← ev_int, map_ev, hL, map_zero])

  have h1 : ∀ b : ℤ, G.eval (Polynomial.C b) = 0 := fun b =>
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem (f := fun a : ℤ => a)
      (fun _ _ h => h) fun a => hZ a b)
  have h2 : G = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun b : ℤ => Polynomial.C b) (fun _ _ h => Polynomial.C_injective h) fun b => h1 b)
  exact sub_eq_zero.mp h2

theorem ev_comm_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) {A : Type*} [CommRing A] (x y : A) :
    ev Φ x y = ev Φ y x := by
  rw [← ev_swap, swap_eq_of_evalSymm h]

section rel
variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffMap_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, jqNModC]

theorem ev_jq_int : ev data.Φ (jqModC ℤ) (jqNModC ℤ N) = 0 := by
  apply coeffMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_ev, coeffMap_jqModC, coeffMap_jqNModC, map_zero, jqModC_rat, jqNModC, jqModC_rat]
  have h0 := data.eval_eq_zero
  rw [evalAtJ_def, aeval_toRingHom_eq] at h0
  exact h0

theorem ev_jq (A : Type*) [CommRing A] : ev data.Φ (jqModC A) (jqNModC A N) = 0 := by
  have h := congrArg (coeffMap (Int.castRingHom A)) (ev_jq_int data)
  rwa [map_ev, coeffMap_jqModC, coeffMap_jqNModC, map_zero] at h

end rel

section slice
variable {A B : Type*} [CommRing A] [CommRing B]

def slice (Φ : Polynomial (Polynomial ℤ)) (x : A) : Polynomial A :=
  (Φ.map (mapRingHom (Int.castRingHom A))).map (evalRingHom x)

theorem eval_slice (Φ : Polynomial (Polynomial ℤ)) (x y : A) : (slice Φ x).eval y = ev Φ x y := by
  rw [slice, map_evalRingHom_eval, ev_eq_evalEval]

theorem slice_monic {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (x : A) : (slice Φ x).Monic :=
  (hΦ.map _).map _

theorem slice_natDegree [Nontrivial A] {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (x : A) :
    (slice Φ x).natDegree = Φ.natDegree := by
  rw [slice, (hΦ.map _).natDegree_map, hΦ.natDegree_map]

theorem slice_map (Φ : Polynomial (Polynomial ℤ)) (x : A) (φ : A →+* B) :
    (slice Φ x).map φ = slice Φ (φ x) := by
  simp only [slice, Polynomial.map_map]
  refine congrArg (fun f : Polynomial ℤ →+* B => Φ.map f) ?_
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

end slice

section roots
variable (K : Type*) [Field K] {N : ℕ} [hN : Fact N.Prime] (data : ModularPolynomialData N)

theorem natDegree_slice (x : LaurentSeries K) : (slice data.Φ x).natDegree = N + 1 := by
  rw [slice_natDegree data.monic, data.natDegree_eq, dedekindPsi_prime hN.out]

variable (hsymm : EvalSymm data.Φ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)

def root (i : Fin (N + 1)) : LaurentSeries K :=
  Fin.cases (qExpand K N (jqNModC K N)) (fun b => qTwist (ζ ^ (b : ℕ)) (jqModC K)) i

theorem root_zero : root K ζ (0 : Fin (N + 1)) = qExpand K N (jqNModC K N) := rfl

theorem root_succ (b : Fin N) : root K ζ b.succ = qTwist (ζ ^ (b : ℕ)) (jqModC K) := rfl

omit hN in
include hζ in
theorem zeta_pow_N : ζ ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)

include hsymm hζ in

theorem isRoot_root (i : Fin (N + 1)) : (slice data.Φ (jqNModC K N)).IsRoot (root K ζ i) := by
  rw [Polynomial.IsRoot, eval_slice]
  refine Fin.cases ?_ (fun b => ?_) i
  ·
    rw [root_zero, jqNModC, ← map_ev, ← jqNModC, ev_jq data K, map_zero]
  ·
    rw [root_succ, ev_comm_of_evalSymm hsymm]
    have hfix : qTwist (ζ ^ (b : ℕ)) (jqNModC K N) = jqNModC K N := by
      rw [jqNModC, qTwist_qExpand, zpow_natCast, ← pow_mul, mul_comm, pow_mul, zeta_pow_N K ζ hζ, one_pow,
        qTwist_one_apply]
    have h := congrArg (qTwist (ζ ^ (b : ℕ))) (ev_jq data K)
    rwa [map_ev, hfix, map_zero] at h

include hζ in

theorem root_injective : Function.Injective (root (N := N) K ζ) := by
  have hN2 : ¬ ((N : ℤ) ∣ (-1 : ℤ)) := fun h => by
    have h1 : (N : ℤ) ∣ 1 := (Int.dvd_neg).mp h
    have := Int.eq_one_of_dvd_one (Int.natCast_nonneg N) h1
    exact hN.out.one_lt.ne' (by exact_mod_cast this)
  have c0 : (root (N := N) K ζ 0).coeff (-1) = 0 := by
    rw [root_zero]; exact qExpand_coeff_of_not_dvd N _ hN2
  have cs : ∀ b : Fin N, (root K ζ b.succ).coeff (-1) = ((ζ ^ (b : ℕ))⁻¹ : Kˣ) := by
    intro b
    rw [root_succ, qTwist_coeff, coeff_jqModC_neg_one, mul_one, zpow_neg, zpow_one]
  intro i i' h
  have hc := congrArg (fun f : LaurentSeries K => f.coeff (-1)) h
  beta_reduce at hc
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨b, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨b', rfl⟩
  · rfl
  · rw [c0, cs] at hc; exact absurd hc.symm (Units.ne_zero _)
  · rw [c0, cs] at hc; exact absurd hc (Units.ne_zero _)
  · rw [cs, cs] at hc
    have h1 : ζ ^ (b : ℕ) = ζ ^ (b' : ℕ) := inv_injective (Units.ext hc)
    have h2 : (ζ : K) ^ (b : ℕ) = (ζ : K) ^ (b' : ℕ) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h1]
    exact congrArg Fin.succ (Fin.ext (hζ.pow_inj b.isLt b'.isLt h2))

include hsymm hζ in

theorem slice_jqNModC_eq_prod :
    slice data.Φ (jqNModC K N) = ∏ i : Fin (N + 1), (Polynomial.X - Polynomial.C (root K ζ i)) := by
  have hdvd : (∏ i : Fin (N + 1), (Polynomial.X - Polynomial.C (root K ζ i))) ∣ slice data.Φ (jqNModC K N) :=
    Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C (root_injective K ζ hζ)).set_pairwise _)
      fun i _ => dvd_iff_isRoot.mpr (isRoot_root K data hsymm ζ hζ i)
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C _ _) (slice_monic data.monic _) hdvd ?_
  rw [natDegree_slice, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]

include hsymm hζ in
theorem slice_jqNModC_separable : (slice data.Φ (jqNModC K N)).Separable := by
  rw [slice_jqNModC_eq_prod K data hsymm ζ hζ]
  exact separable_prod_X_sub_C_iff.mpr (root_injective K ζ hζ)

include hsymm hζ in

theorem slice_jqModC_separable_of_prim : (slice data.Φ (jqModC K)).Separable := by
  rw [← separable_map (qExpand K N), slice_map]
  exact slice_jqNModC_separable K data hsymm ζ hζ

end roots

section Transc
variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]

def qExpandAlg : LaurentSeries K →ₐ[K] LaurentSeries K :=
  { qExpand K p with
    commutes' := fun r => by
      show qExpand K p (algebraMap K (LaurentSeries K) r) = algebraMap K (LaurentSeries K) r
      have h : algebraMap K (LaurentSeries K) r = HahnSeries.C r := by
        have h1 : algebraMap K (PowerSeries K) r = PowerSeries.C r := by simp
        rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
      rw [h]; exact qExpand_C p r }

theorem qExpandAlg_apply (f : LaurentSeries K) : qExpandAlg K p f = qExpand K p f := rfl

theorem transcendental_jqNModC : Transcendental K (jqNModC K p) := by
  rw [transcendental_iff_injective, show jqNModC K p = qExpandAlg K p (jqModC K) from rfl,
    Polynomial.aeval_algHom]
  exact (qExpand_injective (R := K) p).comp (transcendental_iff_injective.mp (transcendental_jqModC K))

variable {K p} in

theorem slice_jqNModC_separable_of_ne_zero (data : ModularPolynomialData p) (hsymm : EvalSymm data.Φ)
    (hpK : (p : K) ≠ 0) : (slice data.Φ (jqNModC K p)).Separable := by
  haveI : NeZero ((p : ℕ) : K) := ⟨hpK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure K) (n := p)
  have hz' : IsPrimitiveRoot ((hz.isUnit (Fact.out : p.Prime).ne_zero).unit : AlgebraicClosure K) p := by
    simpa using hz
  rw [← separable_map (coeffMap (algebraMap K (AlgebraicClosure K))), slice_map, coeffMap_jqNModC]
  exact slice_jqNModC_separable (AlgebraicClosure K) data hsymm _ hz'

end Transc

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

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]

abbrev Fjp : IntermediateField K (LaurentSeries K) := adjoin K ({jqNModC K p} : Set (LaurentSeries K))

abbrev jpF : Fjp K p := ⟨jqNModC K p, mem_adjoin_simple_self K _⟩

def psi : RatFunc K →ₐ[K] LaurentSeries K :=
  RatFunc.liftAlgHom (aeval (jqNModC K p))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (transcendental_jqNModC K p)))

theorem psi_injective : Function.Injective (psi K p) :=
  RatFunc.liftAlgHom_injective _ (transcendental_iff_injective.mp (transcendental_jqNModC K p))

theorem psi_mem (f : RatFunc K) : psi K p f ∈ Fjp K p := by
  rw [← f.num_div_denom, psi, RatFunc.liftAlgHom_apply_div]
  exact (mem_adjoin_simple_iff K _).mpr ⟨_, _, rfl⟩

theorem psi_X : psi K p RatFunc.X = jqNModC K p := by
  rw [psi, RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X]
  simp

def ratFuncEquiv : RatFunc K ≃+* Fjp K p :=
  RingEquiv.ofBijective
    ({ toFun := fun f => ⟨psi K p f, psi_mem K p f⟩
       map_one' := Subtype.ext (map_one (psi K p))
       map_mul' := fun a b => Subtype.ext (map_mul (psi K p) a b)
       map_zero' := Subtype.ext (map_zero (psi K p))
       map_add' := fun a b => Subtype.ext (map_add (psi K p) a b) } : RatFunc K →+* Fjp K p)
    ⟨fun a b hab => psi_injective K p (congrArg Subtype.val hab), by
      rintro ⟨x, hx⟩
      obtain ⟨r, s, rfl⟩ := (mem_adjoin_simple_iff K _).mp hx
      refine ⟨algebraMap _ _ r / algebraMap _ _ s, Subtype.ext ?_⟩
      show psi K p (algebraMap _ _ r / algebraMap _ _ s) = _
      rw [psi, RatFunc.liftAlgHom_apply_div]⟩

theorem ratFuncEquiv_algebraMap (a : K) :
    ratFuncEquiv K p (algebraMap K (RatFunc K) a) = algebraMap K (Fjp K p) a :=
  Subtype.ext (by exact (psi K p).commutes a)

theorem ratFuncEquiv_X : ratFuncEquiv K p RatFunc.X = jpF K p := Subtype.ext (psi_X K p)

theorem eq_congr_placeInfty_of_ord_jF_neg [DecidableEq (RatFunc K)] {w : Place K (Fjp K p)} (hw : w.ord (jpF K p) < 0) :
    w = Place.congrEquiv (ratFuncEquiv K p) (ratFuncEquiv_algebraMap K p) (RationalFunctionField.placeInfty K) := by
  obtain ⟨w₀, rfl⟩ := (Place.congrEquiv (ratFuncEquiv K p) (ratFuncEquiv_algebraMap K p)).surjective w
  congr 1
  apply RationalFunctionField.eq_placeInfty_of_ord_X_neg
  rwa [Place.congrEquiv_apply, ← ratFuncEquiv_X K p, Place.ord_congrRingEquiv] at hw

theorem place_eq_of_ord_jF_neg {v v' : Place K (Fjp K p)} (hv : v.ord (jpF K p) < 0) (hv' : v'.ord (jpF K p) < 0) :
    v = v' := by
  classical
  rw [eq_congr_placeInfty_of_ord_jF_neg K p hv, eq_congr_placeInfty_of_ord_jF_neg K p hv']

theorem ord_jF_eq_neg_one {v : Place K (Fjp K p)} (hv : v.ord (jpF K p) < 0) : v.ord (jpF K p) = -1 := by
  classical
  rw [eq_congr_placeInfty_of_ord_jF_neg K p hv, Place.congrEquiv_apply, ← ratFuncEquiv_X K p, Place.ord_congrRingEquiv,
    ← RatFunc.algebraMap_X, RationalFunctionField.ord_placeInfty_algebraMap X_ne_zero, natDegree_X]
  rfl

abbrev FjpN : IntermediateField (Fjp K p) (LaurentSeries K) := adjoin (Fjp K p) ({jqModC K} : Set (LaurentSeries K))

abbrev jFN : FjpN K p := ⟨jqModC K, mem_adjoin_simple_self _ _⟩

theorem modularFunctionFieldC_eq_restrictScalars :
    modularFunctionFieldC K p = (FjpN K p).restrictScalars K := by
  show adjoin K {jqModC K, jqNModC K p} =
    (adjoin (adjoin K ({jqNModC K p} : Set (LaurentSeries K))) ({jqModC K} : Set (LaurentSeries K))).restrictScalars K
  erw [adjoin_adjoin_left]
  rw [Set.singleton_union, Set.pair_comm]

def toFjpN : modularFunctionFieldC K p ≃+* FjpN K p :=
  (equivOfEq (modularFunctionFieldC_eq_restrictScalars K p)).toRingEquiv.trans
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

theorem toFjpN_algebraMap (a : K) :
    toFjpN K p (algebraMap K (modularFunctionFieldC K p) a) = algebraMap K (FjpN K p) a :=
  Subtype.ext rfl

theorem toFjpN_jC : toFjpN K p ⟨jqModC K, jqModC_mem K p⟩ = jFN K p :=
  Subtype.ext rfl

theorem toFjpN_jpC : toFjpN K p ⟨jqNModC K p, jqNModC_mem K p⟩ = algebraMap (Fjp K p) (FjpN K p) (jpF K p) :=
  Subtype.ext rfl

section Rel
variable {K p}
variable (data : ModularPolynomialData p) (hsymm : EvalSymm data.Φ)

include hsymm in

theorem ev_jpj : ev data.Φ (jqNModC K p) (jqModC K) = 0 := by
  rw [ev_comm_of_evalSymm hsymm]; exact ev_jq data K

include hsymm in

theorem relation_FjpN :
    data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (FjpN K p)) (algebraMap (Fjp K p) (FjpN K p) ((jpF K p)⁻¹)⁻¹))
      (jFN K p) = 0 := by
  apply (algebraMap (FjpN K p) (LaurentSeries K)).injective
  rw [map_zero, inv_inv]
  have h := map_ev (algebraMap (FjpN K p) (LaurentSeries K)) data.Φ
    (algebraMap (Fjp K p) (FjpN K p) (jpF K p)) (jFN K p)
  rw [ev] at h
  rw [h]
  exact ev_jpj data hsymm

theorem relation_C :
    data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (modularFunctionFieldC K p))
      (⟨jqModC K, jqModC_mem K p⟩ : modularFunctionFieldC K p)) ⟨jqNModC K p, jqNModC_mem K p⟩ = 0 := by
  apply (algebraMap (modularFunctionFieldC K p) (LaurentSeries K)).injective
  rw [map_zero]
  have h := map_ev (algebraMap (modularFunctionFieldC K p) (LaurentSeries K)) data.Φ
    (⟨jqModC K, jqModC_mem K p⟩ : modularFunctionFieldC K p) ⟨jqNModC K p, jqNModC_mem K p⟩
  rw [ev] at h
  rw [h]
  exact ev_jq data K

include hsymm in

theorem isIntegral_jqModC : IsIntegral (Fjp K p) (jqModC K) := by
  refine ⟨slice data.Φ (jpF K p), slice_monic data.monic _, ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, slice_map, eval_slice]
  exact ev_jpj data hsymm

set_option synthInstance.maxHeartbeats 800000 in
include hsymm in
theorem finiteDimensional_FjpN : FiniteDimensional (Fjp K p) (FjpN K p) :=
  adjoin.finiteDimensional (isIntegral_jqModC (K := K) data hsymm)

set_option synthInstance.maxHeartbeats 800000 in
include hsymm in
theorem finrank_FjpN_le : Module.finrank (Fjp K p) (FjpN K p) ≤ p + 1 := by
  rw [adjoin.finrank (isIntegral_jqModC (K := K) data hsymm)]
  have h0 : Polynomial.aeval (jqModC K) (slice data.Φ (jpF K p)) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, slice_map, eval_slice]; exact ev_jpj data hsymm
  calc (minpoly (Fjp K p) (jqModC K)).natDegree
      ≤ (slice data.Φ (jpF K p)).natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ h0) (slice_monic data.monic _).ne_zero
    _ = p + 1 := by rw [slice_natDegree data.monic, data.natDegree_eq, dedekindPsi_prime Fact.out]

set_option synthInstance.maxHeartbeats 800000 in
include hsymm in

theorem isSeparable_FjpN (hpK : (p : K) ≠ 0) : Algebra.IsSeparable (Fjp K p) (FjpN K p) := by
  refine (isSeparable_adjoin_simple_iff_isSeparable (Fjp K p) (LaurentSeries K)).mpr ?_
  have hmap : (slice data.Φ (jpF K p)).map (algebraMap (Fjp K p) (LaurentSeries K)) = slice data.Φ (jqNModC K p) :=
    slice_map _ _ _
  have hsep : (slice data.Φ (jpF K p)).Separable :=
    (separable_map (algebraMap (Fjp K p) (LaurentSeries K))).mp (hmap ▸ slice_jqNModC_separable_of_ne_zero data hsymm hpK)
  have h0 : Polynomial.aeval (jqModC K) (slice data.Φ (jpF K p)) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmap, eval_slice]; exact ev_jpj data hsymm
  exact hsep.of_dvd (minpoly.dvd (Fjp K p) _ h0)

end Rel

set_option synthInstance.maxHeartbeats 800000 in
theorem toFjpN_tchart :
    toFjpN K p (⟨jqModC K, jqModC_mem K p⟩ * (⟨jqNModC K p, jqNModC_mem K p⟩ : modularFunctionFieldC K p)⁻¹ ^ p)
      = jFN K p * algebraMap (Fjp K p) (FjpN K p) ((jpF K p)⁻¹ ^ p) := by
  rw [map_mul, map_pow, map_inv₀, toFjpN_jC, toFjpN_jpC, map_pow, map_inv₀]

set_option synthInstance.maxHeartbeats 800000 in

theorem cuspChartZeroInfty_place_unique (hpK : (p : K) ≠ 0) :
    ∀ u u' : Place K (modularFunctionFieldC K p),
      u.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 →
      0 < u.ord (⟨jqModC K, jqModC_mem K p⟩ * (⟨jqNModC K p, jqNModC_mem K p⟩)⁻¹ ^ p) →
      u'.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 →
      0 < u'.ord (⟨jqModC K, jqModC_mem K p⟩ * (⟨jqNModC K p, jqNModC_mem K p⟩)⁻¹ ^ p) → u = u' := by
  intro u u' hu hut hu' hut'
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm p

  obtain ⟨hΦ₁, hΦ₂⟩ := data.weighted_support_le
  have hconv : ∀ w : Place K (modularFunctionFieldC K p), w.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 →
      w.ord ⟨jqNModC K p, jqNModC_mem K p⟩ < 0 := fun w hw =>
    (Place.ord_eq_mul_or_eq_mul_of_modular_support w (Fact.out : p.Prime).pos data.Φ hΦ₁ hΦ₂
      (relation_C data) hw).1
  haveI : FiniteDimensional (Fjp K p) (FjpN K p) := finiteDimensional_FjpN data hsymm
  haveI : Algebra.IsSeparable (Fjp K p) (FjpN K p) := isSeparable_FjpN data hsymm hpK
  have hfin : Module.finrank (Fjp K p) (FjpN K p) ≤ p + 1 := finrank_FjpN_le data hsymm
  set e := toFjpN K p with he_def
  have he := toFjpN_algebraMap K p
  apply (Place.congrEquiv e he).injective
  simp only [Place.congrEquiv_apply]
  have hord : ∀ (w : Place K (modularFunctionFieldC K p)) (f : modularFunctionFieldC K p),
      (Place.congrRingEquiv e he w).ord (e f) = w.ord f := fun w f => Place.ord_congrRingEquiv e he w f
  have hUj : (Place.congrRingEquiv e he u).ord (algebraMap (Fjp K p) (FjpN K p) (jpF K p)) < 0 := by
    rw [← toFjpN_jpC, hord]; exact hconv u hu
  have hU'j : (Place.congrRingEquiv e he u').ord (algebraMap (Fjp K p) (FjpN K p) (jpF K p)) < 0 := by
    rw [← toFjpN_jpC, hord]; exact hconv u' hu'
  have hUt : 0 < (Place.congrRingEquiv e he u).ord (jFN K p * algebraMap (Fjp K p) (FjpN K p) ((jpF K p)⁻¹ ^ p)) := by
    rw [← toFjpN_tchart, hord]; exact hut
  have hU't : 0 < (Place.congrRingEquiv e he u').ord (jFN K p * algebraMap (Fjp K p) (FjpN K p) ((jpF K p)⁻¹ ^ p)) := by
    rw [← toFjpN_tchart, hord]; exact hut'
  exact place_eq_of_vanishing_chart (Fact.out : p.Prime).two_le hfin
    (fun v v' hv hv' => place_eq_of_ord_jF_neg K p hv hv')
    (fun v hv => ord_jF_eq_neg_one K p hv) data.Φ hΦ₁ hΦ₂ (relation_FjpN data hsymm) hUj hUt hU'j hU't

end P2MWs12.CuspTwin

end

p2m_open "ModularCurve~coeffMap_injective" in open AlgebraicCurve  in
theorem solution (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] (hpK : (p : K) ≠ 0) : ∀ u u' : Place K (modularFunctionFieldC K p), u.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 → 0 < u.ord (⟨jqModC K, jqModC_mem K p⟩ * (⟨jqNModC K p, jqNModC_mem K p⟩)⁻¹ ^ p) → u'.ord ⟨jqModC K, jqModC_mem K p⟩ < 0 → 0 < u'.ord (⟨jqModC K, jqModC_mem K p⟩ * (⟨jqNModC K p, jqNModC_mem K p⟩)⁻¹ ^ p) → u = u' :=
  P2MWs12.CuspTwin.cuspChartZeroInfty_place_unique K p hpK

end S_ModularCurve_cuspChartZeroInfty_place_unique
end P2MW
export P2MW.S_ModularCurve_cuspChartZeroInfty_place_unique (solution)
