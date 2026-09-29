-- Prove2me | solution 1 for ModularCurve.finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ba47d0cb-bdd1-5733-acbe-b0b0ee60c75f

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_place_of_ringHom_laurentSeries
import Theorems.Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "IntermediateField HahnSeries ModularCurve~coeffMap_injective"

namespace A9819866d

section Laurent

variable {R S : Type*}

theorem coeff_order_ne_zero' {Γ : Type*} [PartialOrder Γ] [Zero Γ] [Zero R] {x : HahnSeries Γ R}
    (hx : x ≠ 0) : x.coeff x.order ≠ 0 := fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)

theorem order_add_nonneg [Semiring R] {x y : LaurentSeries R} (hx : 0 ≤ x.order) (hy : 0 ≤ y.order) :
    0 ≤ (x + y).order := by
  by_cases hxy : x + y = 0
  · rw [hxy, HahnSeries.order_zero]
  · exact (le_min hx hy).trans (HahnSeries.min_order_le_order_add hxy)

def PosOrd [Semiring R] (x : LaurentSeries R) : Prop := x = 0 ∨ 0 < x.order

theorem posOrd_iff_coeff [Semiring R] (x : LaurentSeries R) :
    PosOrd x ↔ ∀ i ≤ 0, x.coeff i = 0 := by
  constructor
  · rintro (rfl | h) i hi
    · rfl
    · exact HahnSeries.coeff_eq_zero_of_lt_order (hi.trans_lt h)
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · refine Or.inr (lt_of_not_ge fun hle => ?_)
      exact coeff_order_ne_zero' hx (h _ hle)

theorem PosOrd.add [Semiring R] {x y : LaurentSeries R} (hx : PosOrd x) (hy : PosOrd y) :
    PosOrd (x + y) := by
  rw [posOrd_iff_coeff] at *
  intro i hi
  rw [HahnSeries.coeff_add, hx i hi, hy i hi, add_zero]

theorem PosOrd.neg [Ring R] {x : LaurentSeries R} (hx : PosOrd x) : PosOrd (-x) := by
  rw [posOrd_iff_coeff] at *
  intro i hi
  rw [HahnSeries.coeff_neg, hx i hi, neg_zero]

theorem PosOrd.sub [Ring R] {x y : LaurentSeries R} (hx : PosOrd x) (hy : PosOrd y) :
    PosOrd (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem PosOrd.nonneg [Semiring R] {x : LaurentSeries R} (hx : PosOrd x) : 0 ≤ x.order := by
  rcases hx with rfl | h
  · rw [HahnSeries.order_zero]
  · exact h.le

theorem PosOrd.mul_nonneg [Semiring R] [NoZeroDivisors R] {x y : LaurentSeries R} (hx : PosOrd x)
    (hy : 0 ≤ y.order) : PosOrd (x * y) := by
  rcases hx with rfl | h
  · exact Or.inl (zero_mul _)
  by_cases hy0 : y = 0
  · exact Or.inl (by rw [hy0, mul_zero])
  by_cases hx0 : x = 0
  · exact Or.inl (by rw [hx0, zero_mul])
  right
  rw [HahnSeries.order_mul hx0 hy0]
  exact add_pos_of_pos_of_nonneg h hy

theorem posOrd_sub_C_coeff_zero [Ring R] {x : LaurentSeries R} (hx : 0 ≤ x.order) :
    PosOrd (x - HahnSeries.C (x.coeff 0)) := by
  rw [posOrd_iff_coeff]
  intro i hi
  rcases hi.lt_or_eq with h | rfl
  · rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order (h.trans_le hx),
      HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h.ne, sub_zero]
  · rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_self]

theorem eq_zero_of_posOrd_C [Semiring R] {c : R} (h : PosOrd (HahnSeries.C c : LaurentSeries R)) :
    c = 0 := by
  have := (posOrd_iff_coeff _).mp h 0 le_rfl
  rwa [HahnSeries.C_apply, HahnSeries.coeff_single_same] at this

theorem order_inv' {K : Type*} [Field K] (x : LaurentSeries K) : x⁻¹.order = -x.order := by
  by_cases hx : x = 0
  · rw [hx, inv_zero, HahnSeries.order_zero, neg_zero]
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega

theorem order_C_ne [Semiring R] [NoZeroDivisors R] {c : R} (hc : c ≠ 0) :
    (HahnSeries.C c : LaurentSeries R).order = 0 := by
  rw [HahnSeries.C_apply, HahnSeries.order_single hc]

theorem order_add_eq_zero_of_posOrd [Semiring R] {x y : LaurentSeries R} (hx : x ≠ 0)
    (hx0 : x.order = 0) (hy : PosOrd y) : x + y ≠ 0 ∧ (x + y).order = 0 := by
  have hc : (x + y).coeff 0 ≠ 0 := by
    rw [HahnSeries.coeff_add, (posOrd_iff_coeff y).mp hy 0 le_rfl, add_zero, ← hx0]
    exact coeff_order_ne_zero' hx
  have hne : x + y ≠ 0 := fun h => hc (by rw [h, HahnSeries.coeff_zero])
  refine ⟨hne, le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_⟩
  exact (le_min hx0.ge hy.nonneg).trans (HahnSeries.min_order_le_order_add hne)

theorem coeffMap_injective [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem order_coeffMap [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f)
    (x : LaurentSeries R) : (coeffMap f x).order = x.order := by
  by_cases hx : x = 0
  · rw [hx, map_zero, HahnSeries.order_zero, HahnSeries.order_zero]
  have hne : coeffMap f x ≠ 0 := fun h => hx (coeffMap_injective hf (by rw [h, map_zero]))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) (HahnSeries.order_le_of_coeff_ne_zero ?_)
  · rw [coeffMap_coeff]
    exact fun h => coeff_order_ne_zero' hx (hf (by rw [h, map_zero]))
  · intro h
    exact coeff_order_ne_zero' hne (by rw [coeffMap_coeff, h, map_zero])

theorem PosOrd.coeffMap [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f)
    {x : LaurentSeries R} (hx : PosOrd x) : PosOrd (ModularCurve.coeffMap f x) := by
  rcases hx with rfl | h
  · exact Or.inl (map_zero _)
  · exact Or.inr (by rwa [order_coeffMap hf])

theorem coeffMap_C [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    coeffMap f (HahnSeries.C c) = HahnSeries.C (f c) := by
  rw [HahnSeries.C_apply, coeffMap_single, HahnSeries.C_apply]

end Laurent

section RingHomOrder

variable {K F' : Type*} [Field K] [Field F'] (φ : F' →+* LaurentSeries K)

theorem order_map_mul {a b : F'} (ha : a ≠ 0) (hb : b ≠ 0) :
    (φ (a * b)).order = (φ a).order + (φ b).order := by
  rw [map_mul, HahnSeries.order_mul ((map_ne_zero φ).mpr ha) ((map_ne_zero φ).mpr hb)]

theorem order_map_inv (a : F') : (φ a⁻¹).order = -(φ a).order := by
  rw [map_inv₀, order_inv']

theorem order_map_div {a b : F'} (ha : a ≠ 0) (hb : b ≠ 0) :
    (φ (a / b)).order = (φ a).order - (φ b).order := by
  rw [div_eq_mul_inv, order_map_mul φ ha (inv_ne_zero hb), order_map_inv, sub_eq_add_neg]

theorem order_map_pow (a : F') (n : ℕ) : (φ (a ^ n)).order = n * (φ a).order := by
  rw [map_pow, HahnSeries.order_pow, nsmul_eq_mul]

end RingHomOrder

section Engine

variable {k K F F' : Type*} [Field k] [Field K] [Field F] [Field F'] [Algebra k F] [Algebra K F']

structure OverData (ι : k →+* K) (θ : F →+* F') (φ : F' →+* LaurentSeries K) : Prop where
  cmp : ∀ a : k, θ (algebraMap k F a) = algebraMap K F' (ι a)
  gen : ∀ z : F', ∃ a b : F', a ∈ Algebra.adjoin K (Set.range θ) ∧
    b ∈ Algebra.adjoin K (Set.range θ) ∧ z = a / b
  const : ∀ c : K, c ≠ 0 → (φ (algebraMap K F' c)).order = 0
  nc : ∃ a : F, ∀ a₀ : k, a ≠ algebraMap k F a₀
  res : ∀ a : F, 0 ≤ (φ (θ a)).order → ∃ a₀ : k, PosOrd (φ (θ (a - algebraMap k F a₀)))

namespace OverData

variable {ι : k →+* K} {θ : F →+* F'} {φ : F' →+* LaurentSeries K}

omit [Algebra K F'] in
theorem psi_ne_zero (θ : F →+* F') (φ : F' →+* LaurentSeries K) {f : F} (hf : f ≠ 0) :
    φ (θ f) ≠ 0 :=
  (map_ne_zero φ).mpr ((map_ne_zero θ).mpr hf)

omit [Algebra K F'] in
theorem ne_zero_of_order_ne {f : F} (hf : (φ (θ f)).order ≠ 0) : f ≠ 0 := by
  rintro rfl
  rw [map_zero, map_zero, HahnSeries.order_zero] at hf
  exact hf rfl

variable (h : OverData ι θ φ)
include h

theorem exists_order_neg : ∃ f : F, (φ (θ f)).order < 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨a, ha⟩ := h.nc
  obtain ⟨a₀, hpos⟩ := h.res a (hall a)
  have hy0 : a - algebraMap k F a₀ ≠ 0 := sub_ne_zero.mpr (ha a₀)
  have hpos' : 0 < (φ (θ (a - algebraMap k F a₀))).order :=
    hpos.resolve_left (psi_ne_zero θ φ hy0)
  have := hall (a - algebraMap k F a₀)⁻¹
  rw [map_inv₀, order_map_inv] at this
  omega

theorem exists_unif : ∃ π : F, 0 < (φ (θ π)).order ∧
    ∀ f : F, f ≠ 0 → (φ (θ π)).order ∣ (φ (θ f)).order := by
  let H : AddSubgroup ℤ :=
    { carrier := {m | ∃ f : F, f ≠ 0 ∧ (φ (θ f)).order = m}
      zero_mem' := ⟨1, one_ne_zero, by rw [map_one, map_one, HahnSeries.order_one]⟩
      add_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f * g, mul_ne_zero hf hg, by
          rw [map_mul, order_map_mul φ ((map_ne_zero θ).mpr hf) ((map_ne_zero θ).mpr hg)]⟩
      neg_mem' := by
        rintro _ ⟨f, hf, rfl⟩
        exact ⟨f⁻¹, inv_ne_zero hf, by rw [map_inv₀, order_map_inv]⟩ }
  have hmem : ∀ f : F, f ≠ 0 → (φ (θ f)).order ∈ H := fun f hf => ⟨f, hf, rfl⟩
  obtain ⟨g, hg⟩ := Int.subgroup_cyclic H
  have hgH : g ∈ H := by rw [hg]; exact AddSubgroup.subset_closure rfl
  obtain ⟨fg, hfg0, hfg⟩ := hgH
  have hmul : ∀ f : F, f ≠ 0 → g ∣ (φ (θ f)).order := fun f hf => by
    have := hmem f hf
    rw [hg, AddSubgroup.mem_closure_singleton] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by rw [← hn, smul_eq_mul, mul_comm]⟩
  obtain ⟨f₀, hf₀⟩ := h.exists_order_neg
  have hf₀0 : f₀ ≠ 0 := ne_zero_of_order_ne hf₀.ne
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hmul f₀ hf₀0
    rw [zero_mul] at hc
    omega
  rcases lt_or_gt_of_ne hg0 with hlt | hgt
  · refine ⟨fg⁻¹, ?_, fun f hf => ?_⟩
    · rw [map_inv₀, order_map_inv, hfg]; omega
    · rw [map_inv₀, order_map_inv, hfg]; exact (neg_dvd).mpr (hmul f hf)
  · exact ⟨fg, by rw [hfg]; exact hgt, fun f hf => by rw [hfg]; exact hmul f hf⟩

omit [Algebra K F'] h in

theorem nonneg_inv_unif_mul {π : F} (hπ : ∀ f : F, f ≠ 0 → (φ (θ π)).order ∣ (φ (θ f)).order)
    {m : F} (hm : PosOrd (φ (θ m))) : 0 ≤ (φ (θ (π⁻¹ * m))).order := by
  by_cases hm0 : m = 0
  · rw [hm0, mul_zero, map_zero, map_zero, HahnSeries.order_zero]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hπ m hm0
    rw [map_zero, map_zero, HahnSeries.order_zero, zero_mul] at hc
    exact (hm.resolve_left (psi_ne_zero θ φ hm0)).ne' hc
  rw [map_mul, order_map_mul φ ((map_ne_zero θ).mpr (inv_ne_zero hπ0)) ((map_ne_zero θ).mpr hm0),
    map_inv₀, order_map_inv]
  have := Int.le_of_dvd (hm.resolve_left (psi_ne_zero θ φ hm0)) (hπ m hm0)
  omega

omit h in

def RSpan (θ : F →+* F') (φ : F' →+* LaurentSeries K) : Submodule K F' :=
  Submodule.span K (θ '' {f : F | 0 ≤ (φ (θ f)).order})

omit h in
theorem mem_RSpan_of {f : F} (hf : 0 ≤ (φ (θ f)).order) : θ f ∈ RSpan (K := K) θ φ :=
  Submodule.subset_span ⟨f, hf, rfl⟩

omit h in
theorem one_mem_RSpan : (1 : F') ∈ RSpan (K := K) θ φ := by
  have := mem_RSpan_of (K := K) (θ := θ) (φ := φ) (f := 1)
    (by rw [map_one, map_one, HahnSeries.order_one])
  rwa [map_one] at this

omit h in

theorem nonneg_of_mem_RSpan (φ'' : F' →+* LaurentSeries K)
    (hc'' : ∀ c : K, c ≠ 0 → (φ'' (algebraMap K F' c)).order = 0)
    (hO'' : ∀ f : F, 0 ≤ (φ (θ f)).order → 0 ≤ (φ'' (θ f)).order)
    {r : F'} (hr : r ∈ RSpan (K := K) θ φ) : 0 ≤ (φ'' r).order := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact hO'' f hf
  | zero => rw [map_zero, HahnSeries.order_zero]
  | add x y _ _ hx hy => rw [map_add]; exact order_add_nonneg hx hy
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul]
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero, zero_mul, HahnSeries.order_zero]
    by_cases hx0 : φ'' x = 0
    · rw [hx0, mul_zero, HahnSeries.order_zero]
    rw [HahnSeries.order_mul ((map_ne_zero φ'').mpr ((map_ne_zero _).mpr hc)) hx0, hc'' c hc,
      zero_add]
    exact hx

omit h in

theorem mul_mem_RSpan {a : F} (ha : 0 ≤ (φ (θ a)).order) {r : F'} (hr : r ∈ RSpan (K := K) θ φ) :
    θ a * r ∈ RSpan (K := K) θ φ := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [← map_mul]
    refine mem_RSpan_of ?_
    by_cases ha0 : a = 0
    · rw [ha0, zero_mul, map_zero, map_zero, HahnSeries.order_zero]
    by_cases hf0 : f = 0
    · rw [hf0, mul_zero, map_zero, map_zero, HahnSeries.order_zero]
    rw [map_mul, order_map_mul φ ((map_ne_zero θ).mpr ha0) ((map_ne_zero θ).mpr hf0)]
    exact add_nonneg ha hf
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

omit h in

theorem mul_mem_RSpan' {r s : F'} (hr : r ∈ RSpan (K := K) θ φ) (hs : s ∈ RSpan (K := K) θ φ) :
    r * s ∈ RSpan (K := K) θ φ := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact mul_mem_RSpan hf hs
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

omit h in

theorem exists_denom {a : F'} (ha : a ∈ Algebra.adjoin K (Set.range θ)) :
    ∃ d : F, d ≠ 0 ∧ 0 ≤ (φ (θ d)).order ∧ θ d * a ∈ RSpan (K := K) θ φ := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    by_cases hf : 0 ≤ (φ (θ f)).order
    · exact ⟨1, one_ne_zero, by rw [map_one, map_one, HahnSeries.order_one],
        by rw [map_one, one_mul]; exact mem_RSpan_of hf⟩
    · have hf0 : f ≠ 0 := ne_zero_of_order_ne (fun h0 => hf h0.ge)
      refine ⟨f⁻¹, inv_ne_zero hf0, ?_, ?_⟩
      · rw [map_inv₀, order_map_inv]; omega
      · rw [← map_mul, inv_mul_cancel₀ hf0, map_one]; exact one_mem_RSpan
  | algebraMap c =>
    refine ⟨1, one_ne_zero, by rw [map_one, map_one, HahnSeries.order_one], ?_⟩
    rw [map_one, one_mul, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c one_mem_RSpan
  | add x y _ _ hx hy =>
    obtain ⟨da, hda0, hda, hxa⟩ := hx
    obtain ⟨db, hdb0, hdb, hyb⟩ := hy
    refine ⟨da * db, mul_ne_zero hda0 hdb0, ?_, ?_⟩
    · rw [map_mul, order_map_mul φ ((map_ne_zero θ).mpr hda0) ((map_ne_zero θ).mpr hdb0)]
      exact add_nonneg hda hdb
    · have : θ (da * db) * (x + y) = θ db * (θ da * x) + θ da * (θ db * y) := by
        rw [map_mul]; ring
      rw [this]
      exact Submodule.add_mem _ (mul_mem_RSpan hdb hxa) (mul_mem_RSpan hda hyb)
  | mul x y _ _ hx hy =>
    obtain ⟨da, hda0, hda, hxa⟩ := hx
    obtain ⟨db, hdb0, hdb, hyb⟩ := hy
    refine ⟨da * db, mul_ne_zero hda0 hdb0, ?_, ?_⟩
    · rw [map_mul, order_map_mul φ ((map_ne_zero θ).mpr hda0) ((map_ne_zero θ).mpr hdb0)]
      exact add_nonneg hda hdb
    · have : θ (da * db) * (x * y) = (θ da * x) * (θ db * y) := by
        rw [map_mul]; ring
      rw [this]
      exact mul_mem_RSpan' hxa hyb

theorem exists_const_add {π : F} (hπ0 : π ≠ 0)
    (hπ : ∀ f : F, f ≠ 0 → (φ (θ π)).order ∣ (φ (θ f)).order)
    {r : F'} (hr : r ∈ RSpan (K := K) θ φ) :
    ∃ c : K, ∃ r₁ ∈ RSpan (K := K) θ φ, r = algebraMap K F' c + θ π * r₁ := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨a₀, hpos⟩ := h.res a ha
    have hb := nonneg_inv_unif_mul hπ hpos
    refine ⟨ι a₀, θ (π⁻¹ * (a - algebraMap k F a₀)), mem_RSpan_of hb, ?_⟩
    rw [← h.cmp, ← map_mul, ← map_add, mul_inv_cancel_left₀ hπ0, add_sub_cancel]
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by rw [map_zero, mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c₁, r₁, hr₁, rfl⟩ := hx
    obtain ⟨c₂, r₂, hr₂, rfl⟩ := hy
    exact ⟨c₁ + c₂, r₁ + r₂, Submodule.add_mem _ hr₁ hr₂, by rw [map_add]; ring⟩
  | smul c x _ hx =>
    obtain ⟨c₁, r₁, hr₁, rfl⟩ := hx
    refine ⟨c * c₁, c • r₁, Submodule.smul_mem _ c hr₁, ?_⟩
    rw [smul_add, Algebra.smul_def, Algebra.smul_def, map_mul, Algebra.smul_def]
    ring

theorem exists_normal_form {π : F} (hπe : 0 < (φ (θ π)).order)
    (hπ : ∀ f : F, f ≠ 0 → (φ (θ π)).order ∣ (φ (θ f)).order) :
    ∀ (n : ℕ) {r : F'}, r ∈ RSpan (K := K) θ φ → r ≠ 0 → (φ r).order.toNat = n →
    ∃ (m : ℕ) (c : K) (y : F'), c ≠ 0 ∧ y ∈ RSpan (K := K) θ φ ∧
      r = θ π ^ m * (algebraMap K F' c + θ π * y) := by
  have hπ0 : π ≠ 0 := ne_zero_of_order_ne hπe.ne'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro r hr hr0 hn
  obtain ⟨c, r₁, hr₁, hrr⟩ := h.exists_const_add hπ0 hπ hr
  by_cases hc : c = 0
  · rw [hc, map_zero, zero_add] at hrr
    have hr₁0 : r₁ ≠ 0 := by rintro rfl; exact hr0 (by rw [hrr, mul_zero])
    have hφr₁ : 0 ≤ (φ r₁).order := nonneg_of_mem_RSpan φ h.const (fun _ hf => hf) hr₁
    have hord : (φ r).order = (φ (θ π)).order + (φ r₁).order := by
      rw [hrr, map_mul, HahnSeries.order_mul (psi_ne_zero θ φ hπ0) ((map_ne_zero φ).mpr hr₁0)]
    have hlt : (φ r₁).order.toNat < n := by
      rw [← hn]; omega
    obtain ⟨m, c', y, hc', hy, hr₁eq⟩ := ih _ hlt hr₁ hr₁0 rfl
    exact ⟨m + 1, c', y, hc', hy, by rw [hrr, hr₁eq, pow_succ]; ring⟩
  · exact ⟨0, c, r₁, hc, hr₁, by rw [pow_zero, one_mul]; exact hrr⟩

omit h in

theorem order_eq_of_normal_form (φ'' : F' →+* LaurentSeries K)
    (hc'' : ∀ c : K, c ≠ 0 → (φ'' (algebraMap K F' c)).order = 0)
    (hO'' : ∀ f : F, 0 ≤ (φ (θ f)).order → 0 ≤ (φ'' (θ f)).order)
    {π : F} (hπ'' : 0 < (φ'' (θ π)).order)
    {m : ℕ} {c : K} {y : F'} (hc : c ≠ 0) (hy : y ∈ RSpan (K := K) θ φ) :
    (φ'' (θ π ^ m * (algebraMap K F' c + θ π * y))).order = m * (φ'' (θ π)).order := by
  have hu := order_add_eq_zero_of_posOrd ((map_ne_zero φ'').mpr ((map_ne_zero _).mpr hc))
    (hc'' c hc) (PosOrd.mul_nonneg (Or.inr hπ'') (nonneg_of_mem_RSpan φ'' hc'' hO'' hy))
  rw [← map_mul, ← map_add] at hu
  have hπ0 : θ π ≠ 0 := by
    intro h0; rw [h0, map_zero, HahnSeries.order_zero] at hπ''; exact lt_irrefl _ hπ''
  rw [map_mul, HahnSeries.order_mul ((map_ne_zero φ'').mpr (pow_ne_zero _ hπ0)) hu.1, hu.2, add_zero,
    order_map_pow]

theorem sign_agree (z : F') (hz : z ≠ 0) :
    ∃ (mA mB : ℕ), (∀ ψ : F' →+* LaurentSeries K,
      (∀ c : K, c ≠ 0 → (ψ (algebraMap K F' c)).order = 0) →
      (∀ f : F, 0 ≤ (ψ (θ f)).order ↔ 0 ≤ (φ (θ f)).order) →
      ∃ π : F, 0 < (ψ (θ π)).order ∧ (ψ z).order = ((mA : ℤ) - mB) * (ψ (θ π)).order) := by
  obtain ⟨π, hπe, hπ⟩ := h.exists_unif
  have hπ0 : π ≠ 0 := ne_zero_of_order_ne hπe.ne'
  obtain ⟨a, b, ha, hb, rfl⟩ := h.gen z
  have ha0 : a ≠ 0 := by rintro rfl; exact hz (zero_div _)
  have hb0 : b ≠ 0 := by rintro rfl; exact hz (div_zero _)
  obtain ⟨da, hda0, hda, hA⟩ := exists_denom ha
  obtain ⟨db, hdb0, hdb, hB⟩ := exists_denom hb
  have hA' := mul_mem_RSpan hdb hA
  have hB' := mul_mem_RSpan hda hB
  have hA0 : θ db * (θ da * a) ≠ 0 :=
    mul_ne_zero ((map_ne_zero θ).mpr hdb0) (mul_ne_zero ((map_ne_zero θ).mpr hda0) ha0)
  have hB0 : θ da * (θ db * b) ≠ 0 :=
    mul_ne_zero ((map_ne_zero θ).mpr hda0) (mul_ne_zero ((map_ne_zero θ).mpr hdb0) hb0)
  have heq : a / b = (θ db * (θ da * a)) / (θ da * (θ db * b)) := by
    rw [show θ da * (θ db * b) = θ db * (θ da * b) by ring,
      mul_div_mul_left _ _ ((map_ne_zero θ).mpr hdb0), mul_div_mul_left _ _ ((map_ne_zero θ).mpr hda0)]
  obtain ⟨mA, cA, yA, hcA, hyA, hAeq⟩ := h.exists_normal_form hπe hπ _ hA' hA0 rfl
  obtain ⟨mB, cB, yB, hcB, hyB, hBeq⟩ := h.exists_normal_form hπe hπ _ hB' hB0 rfl
  refine ⟨mA, mB, fun ψ hcψ hiffψ => ?_⟩
  have hOψ : ∀ f : F, 0 ≤ (φ (θ f)).order → 0 ≤ (ψ (θ f)).order := fun f hf => (hiffψ f).mpr hf
  have hπψ : 0 < (ψ (θ π)).order := by
    have h1 : ¬ 0 ≤ (φ (θ π⁻¹)).order := by rw [map_inv₀, order_map_inv]; omega
    rw [← hiffψ] at h1
    rw [map_inv₀, order_map_inv] at h1
    omega
  refine ⟨π, hπψ, ?_⟩
  rw [heq, order_map_div ψ hA0 hB0, hAeq, hBeq, order_eq_of_normal_form ψ hcψ hOψ hπψ hcA hyA,
    order_eq_of_normal_form ψ hcψ hOψ hπψ hcB hyB]
  ring

theorem nonneg_iff (φ'' : F' →+* LaurentSeries K)
    (hc'' : ∀ c : K, c ≠ 0 → (φ'' (algebraMap K F' c)).order = 0)
    (hiff : ∀ f : F, 0 ≤ (φ'' (θ f)).order ↔ 0 ≤ (φ (θ f)).order) (z : F') :
    0 ≤ (φ'' z).order ↔ 0 ≤ (φ z).order := by
  by_cases hz : z = 0
  · rw [hz, map_zero, map_zero]
  obtain ⟨mA, mB, hall⟩ := h.sign_agree z hz
  obtain ⟨π₁, hπ₁, h₁⟩ := hall φ'' hc'' hiff
  obtain ⟨π₂, hπ₂, h₂⟩ := hall φ h.const (fun _ => Iff.rfl)
  rw [h₁, h₂, mul_nonneg_iff_of_pos_right hπ₁, mul_nonneg_iff_of_pos_right hπ₂]

theorem exists_order_eq_one (ht : ∃ t : F', (φ t).order = 1) : ∃ π : F, (φ (θ π)).order = 1 := by
  obtain ⟨t, ht⟩ := ht
  have ht0 : t ≠ 0 := by rintro rfl; rw [map_zero, HahnSeries.order_zero] at ht; exact zero_ne_one ht
  obtain ⟨mA, mB, hall⟩ := h.sign_agree t ht0
  obtain ⟨π, hπ, hπt⟩ := hall φ h.const (fun _ => Iff.rfl)
  refine ⟨π, ?_⟩
  rw [ht] at hπt
  have hdvd : (φ (θ π)).order ∣ 1 := ⟨(mA : ℤ) - mB, by rw [hπt, mul_comm]⟩
  exact Int.eq_one_of_dvd_one hπ.le hdvd

end OverData

end Engine

section FunctionField

variable (K : Type*) [Field K] (N : ℕ)

def jGen : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

@[scoped simp] theorem coe_jGen : (jGen K N : LaurentSeries K) = jqModC K := rfl

def jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) : modularFunctionFieldFullC K N :=
  ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩

@[scoped simp] theorem coe_jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) :
    (jGenD K N d hd : LaurentSeries K) = qExpand K d (jqModC K) := rfl

theorem transcendental_jGen : Transcendental K (jGen K N) := by
  rw [← transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (modularFunctionFieldFullC K N) (LaurentSeries K))]
  exact ModularCurve.transcendental_jqModC K

def gensC : Set (modularFunctionFieldFullC K N) := Subtype.val ⁻¹' divisorExpansionsC K N

theorem image_gensC : Subtype.val '' gensC K N = divisorExpansionsC K N := by
  rw [gensC, Set.image_preimage_eq_iff]
  rintro x ⟨d, hne, hd, rfl⟩
  exact ⟨⟨_, @jqModCd_mem_full K _ N d hne hd⟩, rfl⟩

theorem adjoin_gensC_eq_top : adjoin K (gensC K N) = ⊤ := by
  apply lift_injective
  have h1 := IntermediateField.lift_adjoin K (modularFunctionFieldFullC K N) (gensC K N)
  have h2 := IntermediateField.lift_top K (modularFunctionFieldFullC K N)
  rw [image_gensC] at h1
  exact h1.trans h2.symm

end FunctionField

section PartB
open AlgebraicCurve
open scoped Pointwise

section CoeffAction

variable (K : Type*) [Field K] (N : ℕ)

theorem coeffMap_mem_full (f : K →+* K) {x : LaurentSeries K}
    (hx : x ∈ modularFunctionFieldFullC K N) : coeffMap f x ∈ modularFunctionFieldFullC K N := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hne, hdvd, rfl⟩ := hy
    haveI := hne
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdvd
  | algebraMap c =>
    rw [coeffMap_algebraMap]
    exact (modularFunctionFieldFullC K N).algebraMap_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

def coeffEndo (f : K →+* K) : modularFunctionFieldFullC K N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨coeffMap f (x : LaurentSeries K), coeffMap_mem_full K N f x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem coeffEndo_comp (f g : K →+* K) :
    (coeffEndo K N g).comp (coeffEndo K N f) = coeffEndo K N (g.comp f) :=
  RingHom.ext fun x => Subtype.ext (coeffMap_coeffMap g f (x : LaurentSeries K))

theorem coeffEndo_id : coeffEndo K N (RingHom.id K) = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (coeffMap_id (x : LaurentSeries K))

def coeffAut (e : K ≃+* K) : modularFunctionFieldFullC K N ≃+* modularFunctionFieldFullC K N :=
  RingEquiv.ofRingHom (coeffEndo K N (e : K →+* K)) (coeffEndo K N (e.symm : K →+* K))
    (by rw [coeffEndo_comp, ← coeffEndo_id]; congr 1; ext a; simp)
    (by rw [coeffEndo_comp, ← coeffEndo_id]; congr 1; ext a; simp)

def coeffSemilinear (e : K ≃+* K) : SemilinearAut K (modularFunctionFieldFullC K N) :=
  ⟨(coeffAut K N e, e), fun a => Subtype.ext (by
    show coeffMap (e : K →+* K) (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) (e a)
    exact coeffMap_algebraMap (e : K →+* K) a)⟩

end CoeffAction

section ArithFrobenius

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

def arithFrob : SemilinearAut K (modularFunctionFieldFullC K N) :=
  coeffSemilinear K N (frobeniusEquiv K ℓ)

theorem coe_arithFrob_smul (x : modularFunctionFieldFullC K N) :
    ((arithFrob K N ℓ • x : modularFunctionFieldFullC K N) : LaurentSeries K) =
      coeffMap (frobenius K ℓ) (x : LaurentSeries K) := by
  show coeffMap ((frobeniusEquiv K ℓ : K ≃+* K) : K →+* K) (x : LaurentSeries K) = _
  congr 1

theorem frobeniusModL_arithFrob_smul (x : modularFunctionFieldFullC K N) :
    frobeniusModL K N ℓ (arithFrob K N ℓ • x) = x ^ ℓ := by
  apply Subtype.ext
  rw [coe_frobeniusModL, coe_arithFrob_smul, ← ModularCurve.coeffMap_qExpand]
  push_cast
  exact (pow_char_eq_coeffMap_frobenius_qExpand ℓ (x : LaurentSeries K)).symm

theorem pow_mem_valuationSubring_iff {F : Type*} [Field F] (O : ValuationSubring F) (y : F)
    {m : ℕ} (hm : m ≠ 0) : y ^ m ∈ O ↔ y ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hm

theorem frobeniusPlaceModL_eq_smul (w : Place K (modularFunctionFieldFullC K N)) :
    frobeniusPlaceModL K N ℓ w = arithFrob K N ℓ • w := by
  ext x
  rw [mem_frobeniusPlaceModL_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_lhs => rw [← smul_inv_smul (arithFrob K N ℓ) x, frobeniusModL_arithFrob_smul]
  exact pow_mem_valuationSubring_iff _ _ (Fact.out : ℓ.Prime).ne_zero

theorem frobeniusPlaceModL_iterate_eq_smul (n : ℕ) (w : Place K (modularFunctionFieldFullC K N)) :
    (frobeniusPlaceModL K N ℓ)^[n] w = arithFrob K N ℓ ^ n • w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobeniusPlaceModL_eq_smul, smul_smul, ← pow_succ']

theorem fixedPoints_frobeniusPlaceModL_iterate (n : ℕ) :
    Function.fixedPoints (frobeniusPlaceModL K N ℓ)^[n] =
      MulAction.fixedBy (Place K (modularFunctionFieldFullC K N)) (arithFrob K N ℓ ^ n) := by
  ext w
  rw [Function.mem_fixedPoints, Function.IsFixedPt, frobeniusPlaceModL_iterate_eq_smul,
    MulAction.mem_fixedBy]

theorem coe_arithFrob_pow_smul (n : ℕ) (x : modularFunctionFieldFullC K N) :
    ((arithFrob K N ℓ ^ n • x : modularFunctionFieldFullC K N) : LaurentSeries K) =
      coeffMap (iterateFrobenius K ℓ n) (x : LaurentSeries K) := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, one_smul]
    exact (coeffMap_congr (iterateFrobenius_zero (R := K) (p := ℓ)).symm _ ▸ (coeffMap_id _).symm)
  | succ n ih =>
    rw [pow_succ, mul_smul, ih, coe_arithFrob_smul, coeffMap_coeffMap]
    refine coeffMap_congr (RingHom.ext fun a => ?_) _
    rw [RingHom.comp_apply, iterateFrobenius_def, iterateFrobenius_def, frobenius_def, ← pow_mul,
      ← pow_succ']

theorem arithFrob_pow_smul_algebraMap (n : ℕ) (c : K) :
    arithFrob K N ℓ ^ n • algebraMap K (modularFunctionFieldFullC K N) c =
      algebraMap K (modularFunctionFieldFullC K N) (c ^ ℓ ^ n) := by
  apply Subtype.ext
  rw [coe_arithFrob_pow_smul]
  show coeffMap _ (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) _
  rw [coeffMap_algebraMap, iterateFrobenius_def]

end ArithFrobenius

end PartB

section Square

open AlgebraicCurve

variable {k : Type*} [Field k] (K : Type*) [Field K] (ι : k →+* K) (N : ℕ)

theorem coeffMap_mem_full_of_hom {x : LaurentSeries k} (hx : x ∈ modularFunctionFieldFullC k N) :
    coeffMap ι x ∈ modularFunctionFieldFullC K N := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hne, hdvd, rfl⟩ := hy
    haveI := hne
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdvd
  | algebraMap c =>
    rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (modularFunctionFieldFullC K N).algebraMap_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

def theta : modularFunctionFieldFullC k N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨coeffMap ι (x : LaurentSeries k), coeffMap_mem_full_of_hom K ι N x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_theta (x : modularFunctionFieldFullC k N) :
    (theta K ι N x : LaurentSeries K) = coeffMap ι x := rfl

theorem theta_algebraMap (a : k) :
    theta K ι N (algebraMap k _ a) = algebraMap K (modularFunctionFieldFullC K N) (ι a) := by
  apply Subtype.ext
  show coeffMap ι (algebraMap k (LaurentSeries k) a) = algebraMap K (LaurentSeries K) (ι a)
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]

theorem theta_jGenD (d : ℕ) [NeZero d] (hd : d ∣ N) : theta K ι N (jGenD k N d hd) = jGenD K N d hd :=
  Subtype.ext (by rw [coe_theta, coe_jGenD, coe_jGenD, ModularCurve.coeffMap_qExpand, coeffMap_jqModC])

theorem gen_theta (z : modularFunctionFieldFullC K N) :
    ∃ a b : modularFunctionFieldFullC K N, a ∈ Algebra.adjoin K (Set.range (theta K ι N)) ∧
      b ∈ Algebra.adjoin K (Set.range (theta K ι N)) ∧ z = a / b := by
  have hz : z ∈ (⊤ : IntermediateField K (modularFunctionFieldFullC K N)) := mem_top
  rw [← adjoin_gensC_eq_top, ← IntermediateField.mem_toSubfield, adjoin_toSubfield,
    Subfield.mem_closure_iff] at hz
  obtain ⟨y, hy, w, hw, hyw⟩ := hz
  have hsub : Subring.closure (Set.range (algebraMap K _) ∪ gensC K N) ≤
      (Algebra.adjoin K (Set.range (theta K ι N))).toSubring := by
    rw [Subring.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact Subalgebra.algebraMap_mem _ c
    · obtain ⟨d, hne, hd, hxd⟩ := hx
      haveI := hne
      refine Algebra.subset_adjoin ⟨jGenD k N d hd, ?_⟩
      rw [theta_jGenD]
      exact Subtype.ext hxd.symm
  exact ⟨y, w, hsub hy, hsub hw, hyw.symm⟩

theorem jGen_ne_algebraMap (a₀ : k) : jGen k N ≠ algebraMap k _ a₀ :=
  fun h => transcendental_jGen k N (h ▸ isAlgebraic_algebraMap a₀)

theorem nc_theta : ∃ a : modularFunctionFieldFullC k N, ∀ a₀ : k, a ≠ algebraMap k _ a₀ :=
  ⟨jGen k N, jGen_ne_algebraMap N⟩

theorem arithFrob_pow_smul_theta (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] (n : ℕ)
    (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a) (x : modularFunctionFieldFullC k N) :
    arithFrob K N ℓ ^ n • theta K ι N x = theta K ι N x := by
  apply Subtype.ext
  rw [coe_arithFrob_pow_smul, coe_theta, coeffMap_coeffMap]
  refine coeffMap_congr (RingHom.ext fun a => ?_) _
  rw [RingHom.comp_apply, iterateFrobenius_def, hpow]

open Polynomial in

theorem mem_range_of_pow_eq [Finite k] {q : ℕ} (hcard' : Nat.card k = q) (hq : 1 < q) {c : K}
    (hc : c ^ q = c) : ∃ a : k, ι a = c := by
  classical
  haveI := Fintype.ofFinite k
  have hcard : Fintype.card k = q := by rw [← Nat.card_eq_fintype_card, hcard']
  set P : K[X] := X ^ q - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hroot : ∀ x : K, x ∈ P.roots.toFinset ↔ x ^ q = x := fun x => by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
  have hsub : Finset.univ.image ι ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    rw [hroot, ← map_pow, ← hcard, FiniteField.pow_card]
  have hcardim : (Finset.univ.image ι).card = q := by
    rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ, hcard]
  have hle : P.roots.toFinset.card ≤ (Finset.univ.image ι).card :=
    hcardim ▸ ((Multiset.toFinset_card_le _).trans (hdeg ▸ card_roots' P))
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hc' : c ∈ P.roots.toFinset := (hroot c).mpr hc
  rw [← heq] at hc'
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc'
  exact ⟨a, rfl⟩

end Square

section Descent

open AlgebraicCurve
open scoped Pointwise

variable {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ} [NeZero N]

theorem exists_phi (w : Place K (modularFunctionFieldFullC K N)) :
    ∃ φ : modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K, ∀ x, (φ x).order = w.ord x := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC K N
  have hw : w.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed w
  obtain ⟨t, ht⟩ := Place.exists_ord_eq_one w
  obtain ⟨φ, -, hφ⟩ := Place.exists_algHom_laurentSeries_of_deg_eq_one w hw t ht
  exact ⟨φ, hφ⟩

def phiW (w : Place K (modularFunctionFieldFullC K N)) :
    modularFunctionFieldFullC K N →+* LaurentSeries K :=
  (exists_phi w).choose.toRingHom

theorem order_phiW (w : Place K (modularFunctionFieldFullC K N)) (x : modularFunctionFieldFullC K N) :
    (phiW w x).order = w.ord x :=
  (exists_phi w).choose_spec x

theorem mem_iff_phiW (w : Place K (modularFunctionFieldFullC K N)) (x : modularFunctionFieldFullC K N) :
    x ∈ w.toValuationSubring ↔ 0 ≤ (phiW w x).order := by
  by_cases hx : x = 0
  · subst hx; simp [zero_mem]
  rw [Place.mem_iff_ord_nonneg w hx, order_phiW]

theorem phiW_algebraMap (w : Place K (modularFunctionFieldFullC K N)) (c : K) :
    phiW w (algebraMap K _ c) = HahnSeries.C c := by
  show (exists_phi w).choose (algebraMap K _ c) = _
  rw [AlgHom.commutes, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem phiW_const (w : Place K (modularFunctionFieldFullC K N)) (c : K) (hc : c ≠ 0) :
    (phiW w (algebraMap K _ c)).order = 0 := by
  rw [phiW_algebraMap]; exact order_C_ne hc

theorem posOrd_phiW_iff (w : Place K (modularFunctionFieldFullC K N)) (y : modularFunctionFieldFullC K N) :
    PosOrd (phiW w y) ↔ y = 0 ∨ 0 < w.ord y := by
  unfold PosOrd
  rw [map_eq_zero_iff _ (phiW w).injective, order_phiW]

theorem posOrd_phiW_smul {g : SemilinearAut K (modularFunctionFieldFullC K N)}
    {w : Place K (modularFunctionFieldFullC K N)} (hw : g • w = w) (y : modularFunctionFieldFullC K N) :
    PosOrd (phiW w (g • y)) ↔ PosOrd (phiW w y) := by
  have h : w.ord (g • y) = w.ord y := by
    conv_lhs => rw [← hw]
    exact SemilinearAut.ord_smul g w y
  rw [posOrd_phiW_iff, posOrd_phiW_iff, smul_eq_zero_iff_eq, h]

variable {k : Type*} [Field k] [Finite k] (ι : k →+* K) {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {n : ℕ}

theorem res_of_fixed (hcard : Nat.card k = ℓ ^ n) (hn : n ≠ 0) (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a)
    {w : Place K (modularFunctionFieldFullC K N)} (hw : arithFrob K N ℓ ^ n • w = w)
    (a : modularFunctionFieldFullC k N) (ha : 0 ≤ (phiW w (theta K ι N a)).order) :
    ∃ a₀ : k, PosOrd (phiW w (theta K ι N (a - algebraMap k _ a₀))) := by
  set c := (phiW w (theta K ι N a)).coeff 0 with hc
  have h1 : PosOrd (phiW w (theta K ι N a - algebraMap K _ c)) := by
    rw [map_sub, phiW_algebraMap]; exact posOrd_sub_C_coeff_zero ha
  have h2 : PosOrd (phiW w (theta K ι N a - algebraMap K _ (c ^ ℓ ^ n))) := by
    rw [← arithFrob_pow_smul_theta K ι N ℓ n hpow a, ← arithFrob_pow_smul_algebraMap K N ℓ n c,
      ← smul_sub, posOrd_phiW_smul hw]
    exact h1
  have h3 : c ^ ℓ ^ n = c := by
    have h := h1.sub h2
    rw [← map_sub, sub_sub_sub_cancel_left, ← map_sub, phiW_algebraMap] at h
    exact sub_eq_zero.mp (eq_zero_of_posOrd_C h)
  obtain ⟨a₀, ha₀⟩ :=
    mem_range_of_pow_eq K ι hcard (Nat.one_lt_pow hn (Fact.out : ℓ.Prime).one_lt) h3
  exact ⟨a₀, by rw [map_sub, theta_algebraMap, ha₀]; exact h1⟩

theorem overData_of_fixed (hcard : Nat.card k = ℓ ^ n) (hn : n ≠ 0)
    (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a)
    {w : Place K (modularFunctionFieldFullC K N)} (hw : arithFrob K N ℓ ^ n • w = w) :
    OverData ι (theta K ι N) (phiW w) :=
  { cmp := theta_algebraMap K ι N
    gen := gen_theta K ι N
    const := fun c hc => phiW_const w c hc
    nc := nc_theta N
    res := res_of_fixed ι hcard hn hpow hw }

theorem exists_place_below (hcard : Nat.card k = ℓ ^ n) (hn : n ≠ 0)
    (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a)
    {w : Place K (modularFunctionFieldFullC K N)} (hw : arithFrob K N ℓ ^ n • w = w) :
    ∃ v : Place k (modularFunctionFieldFullC k N), v.deg = 1 ∧
      ∀ f, f ∈ v.toValuationSubring ↔ theta K ι N f ∈ w.toValuationSubring := by
  have hO := overData_of_fixed ι hcard hn hpow hw
  obtain ⟨t, ht⟩ := Place.exists_ord_eq_one w
  obtain ⟨π, hπ⟩ := hO.exists_order_eq_one ⟨t, by rw [order_phiW, ht]⟩
  letI : Algebra k K := ι.toAlgebra
  obtain ⟨v, hvO, -, ιv, hιv⟩ :=
    ModularCurve.exists_place_of_ringHom_laurentSeries (k := k) (K := K)
      ((phiW w).comp (theta K ι N))
      (fun a => by rw [RingHom.comp_apply, theta_algebraMap, phiW_algebraMap]; rfl) ⟨π, hπ⟩
  refine ⟨v, ?_, fun f => by rw [hvO, RingHom.comp_apply, mem_iff_phiW]⟩
  rw [Place.deg_eq_one_iff_surjective_algebraMap_residueField]
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  have hx : 0 ≤ (phiW w (theta K ι N x)).order := by
    have := x.2
    rw [hvO] at this
    exact this
  obtain ⟨a₀, ha₀⟩ := hO.res x hx
  refine ⟨a₀, ?_⟩
  apply (ιv : _ →+* K).injective
  show ιv _ = ιv _
  rw [AlgHom.commutes, hιv]
  rw [map_sub, map_sub, theta_algebraMap, phiW_algebraMap, posOrd_iff_coeff] at ha₀
  have := ha₀ 0 le_rfl
  rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_eq_zero] at this
  exact this.symm

theorem eq_of_fixed (hcard : Nat.card k = ℓ ^ n) (hn : n ≠ 0)
    (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a)
    {w₁ w₂ : Place K (modularFunctionFieldFullC K N)} (hw₂ : arithFrob K N ℓ ^ n • w₂ = w₂)
    (h : ∀ f, theta K ι N f ∈ w₁.toValuationSubring ↔ theta K ι N f ∈ w₂.toValuationSubring) :
    w₁ = w₂ := by
  have key := (overData_of_fixed ι hcard hn hpow hw₂).nonneg_iff (phiW w₁)
    (fun c hc => phiW_const w₁ c hc)
    (fun f => by rw [← mem_iff_phiW, ← mem_iff_phiW]; exact h f)
  ext z
  rw [mem_iff_phiW, mem_iff_phiW]
  exact key z

end Descent

section LinDisj

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem linearIndependent_coeffMap {I : Type*} {u : I → LaurentSeries k}
    (hu : LinearIndependent k u) :
    LinearIndependent K (fun i => coeffMap (algebraMap k K) (u i)) := by
  classical
  rw [linearIndependent_iff'] at hu ⊢
  intro s g hg i hi
  let bK := Module.Basis.ofVectorSpace k K
  let r : I → _ → k := fun j β => bK.repr (g j) β
  let T := s.biUnion fun j => (bK.repr (g j)).support
  have hg' : ∀ j ∈ s, g j = ∑ β ∈ T, r j β • bK β := by
    intro j hj
    conv_lhs => rw [← bK.linearCombination_repr (g j)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _
      (Finset.subset_biUnion_of_mem (fun j => (bK.repr (g j)).support) hj)]
    intro β _; exact zero_smul _ _

  have hcoef : ∀ m : ℤ, ∑ β ∈ T, (∑ j ∈ s, r j β * (u j).coeff m) • bK β = 0 := by
    intro m
    have h0 := congrArg (fun x : LaurentSeries K => x.coeff m) hg
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff,
      HahnSeries.coeff_zero] at h0
    rw [← h0]
    simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hg' j hj, Finset.sum_smul]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self_apply]
    ring
  have hr : ∀ β ∈ T, ∀ j ∈ s, r j β = 0 := by
    intro β hβ
    have h1 : ∀ m : ℤ, ∑ j ∈ s, r j β * (u j).coeff m = 0 := fun m =>
      linearIndependent_iff'.mp bK.linearIndependent T _ (hcoef m) β hβ
    have h2 : ∑ j ∈ s, r j β • u j = 0 := by
      ext m
      simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
      exact h1 m
    exact hu s _ h2
  rw [hg' i hi]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [hr β hβ i hi, zero_smul]

theorem alg_smul_eq {L : Type*} [Field L] (a : L) (x : LaurentSeries L) :
    @HSMul.hSMul L (LaurentSeries L) (LaurentSeries L) (@instHSMul L (LaurentSeries L) Algebra.toSMul)
      a x = a • x := by
  rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]

theorem linearIndependent_iff_alg {L : Type*} [Field L] {I : Type*} (v : I → LaurentSeries L) :
    @LinearIndependent I L (LaurentSeries L) v _ _ Algebra.toModule ↔ LinearIndependent L v := by
  rw [@linearIndependent_iff' I L (LaurentSeries L) _ _ Algebra.toModule v, linearIndependent_iff']
  simp only [alg_smul_eq]

theorem linearIndependent_comp_algHom {F : Type*} [Field F] [Algebra k F] {I : Type*} {b : I → F}
    (hb : LinearIndependent k b) (e₀ : F →ₐ[k] LaurentSeries k) : LinearIndependent k (e₀ ∘ b) := by
  rw [← linearIndependent_iff_alg]
  letI : Module k (LaurentSeries k) := Algebra.toModule
  exact hb.map' e₀.toLinearMap (LinearMap.ker_eq_bot.mpr e₀.injective)

theorem injective_of_linearIndependent_basis {R M M' I : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (b : Module.Basis I R M) (f : M →ₗ[R] M')
    (hf : LinearIndependent R (f ∘ b)) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  rw [← b.linearCombination_repr m, Finsupp.apply_linearCombination] at hm
  have := linearIndependent_iff.mp hf _ hm
  rw [← b.linearCombination_repr m, this, map_zero]

variable {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra K F']

theorem exists_ringHom_extension (θ : F →+* F')
    (hθ : ∀ a : k, θ (algebraMap k F a) = algebraMap K F' (algebraMap k K a))
    (e : F' →ₐ[K] LaurentSeries K) (e₀ : F →ₐ[k] LaurentSeries k)
    (hsq : ∀ f, e (θ f) = coeffMap (algebraMap k K) (e₀ f))
    (hgen : ∀ z : F', ∃ a b : F', a ∈ Algebra.adjoin K (Set.range θ) ∧
      b ∈ Algebra.adjoin K (Set.range θ) ∧ z = a / b)
    (lam : F →ₐ[k] LaurentSeries k) :
    ∃ Λ : F' →+* LaurentSeries K, (∀ f, Λ (θ f) = coeffMap (algebraMap k K) (lam f)) ∧
      ∀ c : K, Λ (algebraMap K F' c) = HahnSeries.C c := by
  classical

  letI algkL : Algebra k (LaurentSeries K) :=
    ((algebraMap K (LaurentSeries K)).comp (algebraMap k K)).toAlgebra
  haveI towkL := @IsScalarTower.of_algebraMap_eq k K (LaurentSeries K) _ _ _ _ _ algkL (fun _ => rfl)
  letI algkF' : Algebra k F' := ((algebraMap K F').comp (algebraMap k K)).toAlgebra
  haveI towkF' := @IsScalarTower.of_algebraMap_eq k K F' _ _ _ _ _ algkF' (fun _ => rfl)

  let θa : F →ₐ[k] F' :=
    ⟨θ, fun a => by
      show θ (algebraMap k F a) = algebraMap K F' (algebraMap k K a)
      exact hθ a⟩
  let lamK : F →ₐ[k] LaurentSeries K :=
    ⟨(coeffMap (algebraMap k K)).comp (lam : F →+* LaurentSeries k), fun a => by
      show coeffMap (algebraMap k K) (lam (algebraMap k F a)) =
        algebraMap K (LaurentSeries K) (algebraMap k K a)
      rw [AlgHom.commutes, algebraMap_laurentSeries_eq_single,
        algebraMap_laurentSeries_eq_single, coeffMap_single]⟩

  let T := TensorProduct k K F
  let α : T →ₐ[K] F' :=
    Algebra.TensorProduct.lift (Algebra.ofId K F') θa fun _ _ => Commute.all _ _
  let β : T →ₐ[K] LaurentSeries K :=
    Algebra.TensorProduct.lift (Algebra.ofId K (LaurentSeries K)) lamK fun _ _ => Commute.all _ _
  have hα1 : ∀ f : F, α (1 ⊗ₜ f) = θ f := fun f => by
    show Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ f) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hβ1 : ∀ f : F, β (1 ⊗ₜ f) = coeffMap (algebraMap k K) (lam f) := fun f => by
    show Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ f) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl

  let bF := Module.Basis.ofVectorSpace k F
  let bT : Module.Basis _ K T := Algebra.TensorProduct.basis K bF
  have hbF0 : LinearIndependent k (e₀ ∘ bF) := linearIndependent_comp_algHom bF.linearIndependent e₀
  have hbFl : LinearIndependent k (lam ∘ bF) := linearIndependent_comp_algHom bF.linearIndependent lam
  have hαinj : Function.Injective α := by
    letI : Module K (LaurentSeries K) := Algebra.toModule
    refine injective_of_linearIndependent_basis bT α.toLinearMap ?_
    refine LinearIndependent.of_comp e.toLinearMap ?_
    have : (e.toLinearMap ∘ (α.toLinearMap ∘ bT)) =
        fun i => coeffMap (algebraMap k K) (e₀ (bF i)) := by
      funext i
      show e (α (bT i)) = _
      rw [Algebra.TensorProduct.basis_apply, hα1, hsq]
    rw [this, linearIndependent_iff_alg]
    exact linearIndependent_coeffMap hbF0
  have hβinj : Function.Injective β := by
    letI : Module K (LaurentSeries K) := Algebra.toModule
    refine injective_of_linearIndependent_basis bT β.toLinearMap ?_
    have : (β.toLinearMap ∘ bT) = fun i => coeffMap (algebraMap k K) (lam (bF i)) := by
      funext i
      show β (bT i) = _
      rw [Algebra.TensorProduct.basis_apply, hβ1]
    rw [this, linearIndependent_iff_alg]
    exact linearIndependent_coeffMap hbFl

  haveI : IsDomain T := Function.Injective.isDomain α.toRingHom hαinj
  letI algTF : Algebra T F' := α.toRingHom.toAlgebra
  have halg : ∀ x : T, algebraMap T F' x = α x := fun _ => rfl
  haveI : FaithfulSMul T F' := (faithfulSMul_iff_algebraMap_injective T F').mpr hαinj
  have hrange : Algebra.adjoin K (Set.range θ) ≤ α.range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨1 ⊗ₜ f, hα1 f⟩
  haveI : IsFractionRing T F' := by
    refine IsFractionRing.of_field T F' fun z => ?_
    obtain ⟨a, b, ha, hb, rfl⟩ := hgen z
    obtain ⟨x, hx⟩ := (AlgHom.mem_range α).mp (hrange ha)
    obtain ⟨y, hy⟩ := (AlgHom.mem_range α).mp (hrange hb)
    exact ⟨x, y, by rw [halg, halg, hx, hy]⟩
  refine ⟨IsFractionRing.lift (K := F') (g := β.toRingHom) hβinj, fun f => ?_, fun c => ?_⟩
  · have : θ f = algebraMap T F' (1 ⊗ₜ f) := by rw [halg, hα1]
    rw [this, IsFractionRing.lift_algebraMap]
    exact hβ1 f
  · have : algebraMap K F' c = algebraMap T F' (c ⊗ₜ 1) := by
      rw [halg]
      show _ = Algebra.TensorProduct.lift _ _ _ (c ⊗ₜ 1)
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl
    rw [this, IsFractionRing.lift_algebraMap]
    show Algebra.TensorProduct.lift _ _ _ (c ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.ofId_apply,
      algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

end LinDisj

section Ascent

open AlgebraicCurve
open scoped Pointwise

variable {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ} [NeZero N]
variable {k : Type*} [Field k] [Finite k] (ι : k →+* K) {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {n : ℕ}

omit [NeZero N] [Finite k] in

theorem exists_fixed_above (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a)
    (v : Place k (modularFunctionFieldFullC k N)) (hv : v.deg = 1) :
    ∃ w : Place K (modularFunctionFieldFullC K N), arithFrob K N ℓ ^ n • w = w ∧
      ∀ f, f ∈ v.toValuationSubring ↔ theta K ι N f ∈ w.toValuationSubring := by
  obtain ⟨t, ht⟩ := Place.exists_ord_eq_one v
  obtain ⟨lam, hlamt, hlam⟩ := Place.exists_algHom_laurentSeries_of_deg_eq_one v hv t ht
  letI : Algebra k K := ι.toAlgebra

  obtain ⟨Λ, hΛθ, hΛc⟩ := exists_ringHom_extension (k := k) (K := K) (theta K ι N)
    (fun a => theta_algebraMap K ι N a) (modularFunctionFieldFullC K N).val
    (modularFunctionFieldFullC k N).val (fun _ => rfl) (gen_theta K ι N) lam
  have hordθ : ∀ f, (Λ (theta K ι N f)).order = v.ord f := fun f => by
    rw [hΛθ, order_coeffMap (algebraMap k K).injective, hlam]

  obtain ⟨w, hwO, -, -⟩ :=
    ModularCurve.exists_place_of_ringHom_laurentSeries (k := K) (K := K) Λ
      (fun a => by rw [hΛc, Algebra.algebraMap_self_apply])
      ⟨theta K ι N t, by
        rw [hΛθ, hlamt, coeffMap_single, map_one, HahnSeries.order_single one_ne_zero]⟩
  have hA : ∀ f, f ∈ v.toValuationSubring ↔ theta K ι N f ∈ w.toValuationSubring := fun f => by
    by_cases hf : f = 0
    · subst hf; simp only [map_zero, zero_mem]
    rw [hwO, hordθ, Place.mem_iff_ord_nonneg v hf]
  refine ⟨w, ?_, hA⟩

  have hO : OverData ι (theta K ι N) Λ :=
    { cmp := theta_algebraMap K ι N
      gen := gen_theta K ι N
      const := fun c hc => by rw [hΛc]; exact order_C_ne hc
      nc := nc_theta N
      res := fun a ha => ⟨(lam a).coeff 0, by
        have h0 : 0 ≤ (lam a).order := by
          rwa [hΛθ, order_coeffMap (algebraMap k K).injective] at ha
        have h1 := (posOrd_sub_C_coeff_zero h0).coeffMap (algebraMap k K).injective
        rw [map_sub, coeffMap_C] at h1
        rw [map_sub, theta_algebraMap, map_sub, hΛθ, hΛc]
        exact h1⟩ }
  set τ := arithFrob K N ℓ ^ n with hτ
  let φ'' : modularFunctionFieldFullC K N →+* LaurentSeries K :=
    Λ.comp (MulSemiringAction.toRingHom _ (modularFunctionFieldFullC K N) τ⁻¹)
  have hφ'' : ∀ z, φ'' z = Λ (τ⁻¹ • z) := fun _ => rfl
  have hc'' : ∀ c : K, c ≠ 0 → (φ'' (algebraMap K _ c)).order = 0 := fun c hc => by
    rw [hφ'', SemilinearAut.smul_algebraMap, hΛc]
    exact order_C_ne ((map_ne_zero _).mpr hc)
  have hinv : ∀ f, τ⁻¹ • theta K ι N f = theta K ι N f := fun f => by
    rw [inv_smul_eq_iff, hτ, arithFrob_pow_smul_theta K ι N ℓ n hpow]
  have hiff : ∀ f, 0 ≤ (φ'' (theta K ι N f)).order ↔ 0 ≤ (Λ (theta K ι N f)).order := fun f => by
    rw [hφ'', hinv]
  have key := hO.nonneg_iff φ'' hc'' hiff
  ext z
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    hwO, hwO, ← hφ'']
  exact key z

theorem finite_ord_ne_zero {L F : Type*} [Field L] [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {f : F} (hf : f ≠ 0) : {v : Place L F | v.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf
  refine D.hasFiniteSupport.subset fun v hv => ?_
  rw [Function.mem_support, hD]
  exact hv

theorem fixedBy_subset (hcard : Nat.card k = ℓ ^ n) (hn : n ≠ 0)
    (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a) :
    MulAction.fixedBy (Place K (modularFunctionFieldFullC K N)) (arithFrob K N ℓ ^ n) ⊆
      {w | w.ord (theta K ι N (jGen k N)) ≠ 0} ∪
        ⋃ a₀ : k, {w | w.ord (theta K ι N (jGen k N - algebraMap k _ a₀)) ≠ 0} := by
  intro w hw
  rw [MulAction.mem_fixedBy] at hw
  by_cases h : 0 ≤ (phiW w (theta K ι N (jGen k N))).order
  · obtain ⟨a₀, ha₀⟩ := res_of_fixed ι hcard hn hpow hw _ h
    refine Or.inr (Set.mem_iUnion.mpr ⟨a₀, ?_⟩)
    rw [posOrd_phiW_iff] at ha₀
    rcases ha₀ with h0 | hpos
    · exact absurd h0 ((map_ne_zero_iff _ (theta K ι N).injective).mpr
        (sub_ne_zero.mpr (jGen_ne_algebraMap N a₀)))
    · exact hpos.ne'
  · left
    rw [not_le, order_phiW] at h
    exact h.ne

theorem finite_fixedBy (hcard : Nat.card k = ℓ ^ n) (hn : n ≠ 0)
    (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a) :
    (MulAction.fixedBy (Place K (modularFunctionFieldFullC K N)) (arithFrob K N ℓ ^ n)).Finite := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldFullC K N
  have hθ0 : ∀ x : modularFunctionFieldFullC k N, x ≠ 0 → theta K ι N x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (theta K ι N).injective).mpr hx
  have hj : jGen k N ≠ 0 := fun h => jGen_ne_algebraMap N (0 : k) (by rw [h, map_zero])
  refine Set.Finite.subset ?_ (fixedBy_subset ι hcard hn hpow)
  exact (finite_ord_ne_zero (hθ0 _ hj)).union (Set.finite_iUnion fun a₀ =>
    finite_ord_ne_zero (hθ0 _ (sub_ne_zero.mpr (jGen_ne_algebraMap N a₀))))

theorem finite_and_card_fixedBy_eq (hcard : Nat.card k = ℓ ^ n) (hn : n ≠ 0)
    (hpow : ∀ a : k, ι a ^ ℓ ^ n = ι a) :
    (MulAction.fixedBy (Place K (modularFunctionFieldFullC K N)) (arithFrob K N ℓ ^ n)).Finite ∧
      Nat.card (MulAction.fixedBy (Place K (modularFunctionFieldFullC K N)) (arithFrob K N ℓ ^ n)) =
        Nat.card {v : Place k (modularFunctionFieldFullC k N) | v.deg = 1} := by
  set S := MulAction.fixedBy (Place K (modularFunctionFieldFullC K N)) (arithFrob K N ℓ ^ n) with hS
  have hmem : ∀ w : S, arithFrob K N ℓ ^ n • (w : Place K (modularFunctionFieldFullC K N)) = w :=
    fun w => MulAction.mem_fixedBy.mp w.2
  let Φ : S → {v : Place k (modularFunctionFieldFullC k N) | v.deg = 1} := fun w =>
    ⟨(exists_place_below ι hcard hn hpow (hmem w)).choose,
      (exists_place_below ι hcard hn hpow (hmem w)).choose_spec.1⟩
  have hΦ : ∀ w : S, ∀ f, f ∈ (Φ w : Place k (modularFunctionFieldFullC k N)).toValuationSubring ↔
      theta K ι N f ∈ (w : Place K (modularFunctionFieldFullC K N)).toValuationSubring :=
    fun w => (exists_place_below ι hcard hn hpow (hmem w)).choose_spec.2
  have hbij : Function.Bijective Φ := by
    constructor
    · intro w₁ w₂ h
      apply Subtype.ext
      refine eq_of_fixed ι hcard hn hpow (hmem w₂) fun f => ?_
      rw [← hΦ w₁, ← hΦ w₂, h]
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, hvw⟩ := exists_fixed_above ι hpow v hv
      refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
      ext f
      rw [hΦ ⟨w, hw⟩, ← hvw]
  exact ⟨finite_fixedBy ι hcard hn hpow, Nat.card_congr (Equiv.ofBijective Φ hbij)⟩

end Ascent

end A9819866d
p2m_reactivate "P2MW.S_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq.A9819866d"

open A9819866d AlgebraicCurve in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (n : ℕ) (hn : 0 < n) :
    (Function.fixedPoints (ModularCurve.frobeniusPlaceModL K N ℓ)^[n]).Finite ∧
      Nat.card (Function.fixedPoints (ModularCurve.frobeniusPlaceModL K N ℓ)^[n]) =
        Nat.card {v : AlgebraicCurve.Place (GaloisField ℓ n)
            (ModularCurve.modularFunctionFieldFullC (GaloisField ℓ n) N) | v.deg = 1} := by
  rw [fixedPoints_frobeniusPlaceModL_iterate K N ℓ n]
  letI := ZMod.algebra K ℓ
  let ι : GaloisField ℓ n →+* K := (IsAlgClosed.lift : GaloisField ℓ n →ₐ[ZMod ℓ] K).toRingHom
  have hcard : Nat.card (GaloisField ℓ n) = ℓ ^ n := GaloisField.card ℓ n hn.ne'
  have hpow : ∀ a : GaloisField ℓ n, ι a ^ ℓ ^ n = ι a := fun a => by
    haveI := Fintype.ofFinite (GaloisField ℓ n)
    rw [← map_pow, ← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
  exact finite_and_card_fixedBy_eq ι hcard hn.ne' hpow

end
p2m_reactivate "P2MW.S_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq.A9819866d"

end S_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq
end P2MW
export P2MW.S_ModularCurve_finite_fixedPoints_frobeniusPlaceModL_iterate_and_card_eq (solution)
