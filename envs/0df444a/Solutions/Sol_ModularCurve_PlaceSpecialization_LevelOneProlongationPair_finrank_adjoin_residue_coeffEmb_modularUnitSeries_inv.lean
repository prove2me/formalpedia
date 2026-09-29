-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0bd67cec-b4b2-5c9f-b4a9-1902901e4139

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_order_residue_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_finrank_adjoin_coeffEmb_modularUnitSeries_inv
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData coeffEmb coeffEmb_mem_laurentBaseChange jqModC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence modularFunctionFieldFullC jqModC_mem_full coeff_jqModC_pow_of_lt coeff_jqModC_neg_one modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull PlaceSpecialization.LevelOneProlongationPair.order_residue_coeffEmb_modularUnitSeries finrank_adjoin_coeffEmb_modularUnitSeries_inv"
namespace UnitDeg
p2m_open "ModularCurve"

theorem sum_ne_zero_and_order_eq_of_order_injOn {Γ : Type*} [LinearOrder Γ] [Zero Γ]
    {R : Type*} [AddCommMonoid R] {α : Type*} (s : Finset α) (g : α → HahnSeries Γ R)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, g i ≠ 0 → g j ≠ 0 → (g i).order = (g j).order → i = j)
    (hex : ∃ i ∈ s, g i ≠ 0) :
    (∑ i ∈ s, g i) ≠ 0 ∧
      ∃ i ∈ s, g i ≠ 0 ∧ (∑ j ∈ s, g j).order = (g i).order ∧
        ∀ j ∈ s, g j ≠ 0 → (g i).order ≤ (g j).order := by
  classical
  have htne : (s.filter fun i => g i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hgi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨i₀, hi₀t, hmin⟩ :=
    Finset.exists_min_image (s.filter fun i => g i ≠ 0) (fun i => (g i).order) htne
  obtain ⟨hi₀s, hgi₀⟩ := Finset.mem_filter.mp hi₀t
  have hmin' : ∀ j ∈ s, g j ≠ 0 → (g i₀).order ≤ (g j).order := fun j hj hgj =>
    hmin j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
  have hcoeff : (∑ j ∈ s, g j).coeff (g i₀).order = (g i₀).coeff (g i₀).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single i₀ (fun j hj hji => ?_) (fun h => (h hi₀s).elim)
    by_cases hgj : g j = 0
    · simp [hgj]
    · exact HahnSeries.coeff_eq_zero_of_lt_order
        (lt_of_le_of_ne (hmin' j hj hgj) fun heq => hji (hinj j hj i₀ hi₀s hgj hgi₀ heq.symm))
  have hc0 : (∑ j ∈ s, g j).coeff (g i₀).order ≠ 0 := by
    rw [hcoeff]
    exact fun h => hgi₀ (HahnSeries.coeff_order_eq_zero.mp h)
  have hne : (∑ j ∈ s, g j) ≠ 0 := by
    intro h
    apply hc0
    simp [h]
  refine ⟨hne, i₀, hi₀s, hgi₀, le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc0) ?_, hmin'⟩
  by_contra hlt
  have hlt' : (∑ j ∈ s, g j).order < (g i₀).order := not_le.mp hlt
  apply (HahnSeries.coeff_order_eq_zero (x := ∑ j ∈ s, g j)).not.mpr hne
  rw [HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  by_cases hgj : g j = 0
  · simp [hgj]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hlt' (hmin' j hj hgj))

theorem eq_zero_of_sum_eq_zero_of_order_injOn {Γ : Type*} [LinearOrder Γ] [Zero Γ]
    {R : Type*} [AddCommMonoid R] {α : Type*} (s : Finset α) (g : α → HahnSeries Γ R)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, g i ≠ 0 → g j ≠ 0 → (g i).order = (g j).order → i = j)
    (hsum : ∑ i ∈ s, g i = 0) : ∀ i ∈ s, g i = 0 := by
  by_contra h
  simp only [not_forall] at h
  obtain ⟨i, hi, hgi⟩ := h
  exact (sum_ne_zero_and_order_eq_of_order_injOn s g hinj ⟨i, hi, hgi⟩).1 hsum

end ModularCurve.UnitDeg

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData coeffEmb coeffEmb_mem_laurentBaseChange jqModC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence modularFunctionFieldFullC jqModC_mem_full coeff_jqModC_pow_of_lt coeff_jqModC_neg_one modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull PlaceSpecialization.LevelOneProlongationPair.order_residue_coeffEmb_modularUnitSeries finrank_adjoin_coeffEmb_modularUnitSeries_inv"
namespace UnitDeg
p2m_open "ModularCurve"

section Laurent

variable {k : Type*} [Field k]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in

theorem algebraMap_eq_C' (c : k) : algebraMap k (LaurentSeries k) c = HahnSeries.C c := by

  first
    | (rw [HahnSeries.algebraMap_apply']; simp; done)
    | (rw [← HahnSeries.C_eq_algebraMap]; done)
    | (ext n; simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single, HahnSeries.coeff_C]; done)

theorem order_algebraMap_mul_of_ne_zero {c : k} (hc : c ≠ 0) {y : LaurentSeries k} (hy : y ≠ 0) :
    (algebraMap k (LaurentSeries k) c * y).order = y.order := by
  rw [algebraMap_eq_C', HahnSeries.order_mul (HahnSeries.C_ne_zero hc) hy, HahnSeries.order_C, zero_add]

theorem aeval_ne_zero_of_order_ne_zero {x : LaurentSeries k} (hx : x.order ≠ 0)
    {p : Polynomial k} (hp : p ≠ 0) :
    Polynomial.aeval x p ≠ 0 ∧
      ∃ j ∈ p.support, (Polynomial.aeval x p).order = (j : ℤ) * x.order := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, HahnSeries.order_zero])
  set g : ℕ → LaurentSeries k := fun i => algebraMap k (LaurentSeries k) (p.coeff i) * x ^ i with hg
  have hterm : ∀ i : ℕ, p.coeff i ≠ 0 → (g i).order = (i : ℤ) * x.order := by
    intro i hi
    simp only [hg]
    rw [order_algebraMap_mul_of_ne_zero hi (pow_ne_zero _ hx0), HahnSeries.order_pow, nsmul_eq_mul]
  have hterm0 : ∀ i : ℕ, g i = 0 ↔ p.coeff i = 0 := by
    intro i
    simp only [hg]
    rw [mul_eq_zero, or_iff_left (pow_ne_zero _ hx0), map_eq_zero]
  have haeval : Polynomial.aeval x p = ∑ i ∈ Finset.range (p.natDegree + 1), g i := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  have hinj : ∀ i ∈ Finset.range (p.natDegree + 1), ∀ j ∈ Finset.range (p.natDegree + 1),
      g i ≠ 0 → g j ≠ 0 → (g i).order = (g j).order → i = j := by
    intro i _ j _ hi hj hij
    rw [Ne, hterm0] at hi hj
    rw [hterm i hi, hterm j hj] at hij
    exact_mod_cast mul_right_cancel₀ hx hij
  have hex : ∃ i ∈ Finset.range (p.natDegree + 1), g i ≠ 0 := by
    refine ⟨p.natDegree, Finset.self_mem_range_succ _, ?_⟩
    rw [Ne, hterm0]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  obtain ⟨hne, i, _, hi, hord, -⟩ :=
    sum_ne_zero_and_order_eq_of_order_injOn _ g hinj hex
  rw [Ne, hterm0] at hi
  rw [haeval]
  exact ⟨hne, i, Polynomial.mem_support_iff.mpr hi, by rw [hord, hterm i hi]⟩

theorem transcendental_of_order_ne_zero {x : LaurentSeries k} (hx : x.order ≠ 0) :
    Transcendental k x := by
  rintro ⟨p, hp, h0⟩
  exact (aeval_ne_zero_of_order_ne_zero hx hp).1 h0

theorem transcendental_of_order_coe_ne_zero {E : IntermediateField k (LaurentSeries k)} {z : E}
    (hz : (z : LaurentSeries k).order ≠ 0) : Transcendental k z := by
  rintro ⟨p, hp, h0⟩
  apply (aeval_ne_zero_of_order_ne_zero hz hp).1
  have h := Polynomial.aeval_algHom_apply E.val z p
  rw [h0, map_zero] at h
  exact h

end Laurent

end ModularCurve.UnitDeg

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData coeffEmb coeffEmb_mem_laurentBaseChange jqModC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence modularFunctionFieldFullC jqModC_mem_full coeff_jqModC_pow_of_lt coeff_jqModC_neg_one modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull PlaceSpecialization.LevelOneProlongationPair.order_residue_coeffEmb_modularUnitSeries finrank_adjoin_coeffEmb_modularUnitSeries_inv"
namespace UnitDeg
p2m_open "ModularCurve"

section Laurent2

variable {k : Type*} [Field k]

open Polynomial in

theorem order_dvd_order_of_mem_adjoin_simple {E : IntermediateField k (LaurentSeries k)} {x : E}
    (hx : (x : LaurentSeries k).order ≠ 0) {c : E}
    (hc : c ∈ IntermediateField.adjoin k ({x} : Set E)) (hc0 : c ≠ 0) :
    (x : LaurentSeries k).order ∣ (c : LaurentSeries k).order := by
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k c).mp hc
  have hval : ∀ p : k[X], E.val (aeval x p) = aeval (x : LaurentSeries k) p := fun p =>
    (aeval_algHom_apply E.val x p).symm
  have hcL : (c : LaurentSeries k) = aeval (x : LaurentSeries k) r / aeval (x : LaurentSeries k) s := by
    have h := congrArg E.val hrs
    rw [map_div₀, hval, hval] at h
    exact h
  have hc0L : (c : LaurentSeries k) ≠ 0 := by
    intro h; apply hc0; exact_mod_cast h
  have hr0 : aeval (x : LaurentSeries k) r ≠ 0 := by
    intro h; apply hc0L; rw [hcL, h, zero_div]
  have hs0 : aeval (x : LaurentSeries k) s ≠ 0 := by
    intro h; apply hc0L; rw [hcL, h, div_zero]
  have hr : r ≠ 0 := by rintro rfl; exact hr0 (map_zero _)
  have hs : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
  obtain ⟨-, jr, -, hjr⟩ := aeval_ne_zero_of_order_ne_zero hx hr
  obtain ⟨-, js, -, hjs⟩ := aeval_ne_zero_of_order_ne_zero hx hs
  have hmul : (c : LaurentSeries k) * aeval (x : LaurentSeries k) s = aeval (x : LaurentSeries k) r := by
    rw [hcL, div_mul_cancel₀ _ hs0]
  have hord := congrArg HahnSeries.order hmul
  rw [HahnSeries.order_mul hc0L hs0, hjr, hjs] at hord
  exact ⟨(jr : ℤ) - js, by linarith⟩

theorem linearIndependent_pow_of_order {E : IntermediateField k (LaurentSeries k)} {x y : E}
    {m : ℕ} (hm : 0 < m) (hx : (x : LaurentSeries k).order = -(m : ℤ))
    (hy : (y : LaurentSeries k).order = -1) :
    LinearIndependent (IntermediateField.adjoin k ({x} : Set E))
      (fun i : Fin m => (y ^ (i : ℕ) : E)) := by
  have hx0 : (x : LaurentSeries k).order ≠ 0 := by
    rw [hx, neg_ne_zero]; exact_mod_cast hm.ne'
  have hy0 : (y : LaurentSeries k) ≠ 0 := fun h => by
    rw [h, HahnSeries.order_zero] at hy; exact absurd hy (by norm_num)
  rw [linearIndependent_iff']
  intro s g hsum i hi

  let G : Fin m → LaurentSeries k := fun i => ((g i : E) : LaurentSeries k) * (y : LaurentSeries k) ^ (i : ℕ)
  have hsumL : ∑ i ∈ s, G i = 0 := by
    have h := congrArg E.val hsum
    simp only [IntermediateField.smul_def, smul_eq_mul, map_sum, map_mul, map_pow, map_zero] at h
    exact h
  have hG0 : ∀ j, G j = 0 ↔ g j = 0 := by
    intro j
    simp only [G, mul_eq_zero, or_iff_left (pow_ne_zero _ hy0)]
    constructor
    · intro h; exact_mod_cast h
    · intro h; rw [h]; rfl
  have hGord : ∀ j, g j ≠ 0 → ∃ t : ℤ, (G j).order = (m : ℤ) * t - (j : ℕ) := by
    intro j hj
    have hgj0 : ((g j : E) : LaurentSeries k) ≠ 0 := fun h => hj (by exact_mod_cast h)
    obtain ⟨t, ht⟩ := order_dvd_order_of_mem_adjoin_simple hx0 (g j).2
      (fun h => hj (Subtype.ext h))
    refine ⟨-t, ?_⟩
    simp only [G]
    rw [HahnSeries.order_mul hgj0 (pow_ne_zero _ hy0), HahnSeries.order_pow, hy, ht, hx]
    simp; ring
  have hinj : ∀ i ∈ s, ∀ j ∈ s, G i ≠ 0 → G j ≠ 0 → (G i).order = (G j).order → i = j := by
    intro i _ j _ hi hj hij
    rw [Ne, hG0] at hi hj
    obtain ⟨ti, hti⟩ := hGord i hi
    obtain ⟨tj, htj⟩ := hGord j hj
    rw [hti, htj] at hij
    have hdvd : (m : ℤ) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := ⟨ti - tj, by linarith⟩
    have habs : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| < (m : ℤ) := by
      rw [abs_sub_lt_iff]; constructor <;> omega
    have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact Fin.ext (by omega)
  have hall := eq_zero_of_sum_eq_zero_of_order_injOn s G hinj hsumL
  exact (hG0 i).mp (hall i hi)

theorem le_rank_adjoin_simple_of_order {E : IntermediateField k (LaurentSeries k)} {x y : E}
    {m : ℕ} (hm : 0 < m) (hx : (x : LaurentSeries k).order = -(m : ℤ))
    (hy : (y : LaurentSeries k).order = -1) :
    (m : Cardinal) ≤ Module.rank (IntermediateField.adjoin k ({x} : Set E)) E := by
  simpa using (linearIndependent_pow_of_order hm hx hy).cardinal_lift_le_rank

theorem le_finrank_adjoin_simple_of_order {E : IntermediateField k (LaurentSeries k)} {x y : E}
    {m : ℕ} (hm : 0 < m) (hx : (x : LaurentSeries k).order = -(m : ℤ))
    (hy : (y : LaurentSeries k).order = -1)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set E)) E] :
    m ≤ Module.finrank (IntermediateField.adjoin k ({x} : Set E)) E := by
  simpa using (linearIndependent_pow_of_order hm hx hy).fintype_card_le_finrank

theorem adjoin_simple_inv_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (z : L) : IntermediateField.adjoin K ({z⁻¹} : Set L) = IntermediateField.adjoin K ({z} : Set L) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self K z))
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K z⁻¹)
    rwa [inv_inv] at h

theorem le_finrank_adjoin_simple_inv_of_order {E : IntermediateField k (LaurentSeries k)} {x y : E}
    {m : ℕ} (hm : 0 < m) (hx : (x : LaurentSeries k).order = -(m : ℤ))
    (hy : (y : LaurentSeries k).order = -1)
    [hfin : FiniteDimensional (IntermediateField.adjoin k ({x⁻¹} : Set E)) E] :
    m ≤ Module.finrank (IntermediateField.adjoin k ({x⁻¹} : Set E)) E := by
  rw [adjoin_simple_inv_eq] at hfin ⊢
  exact le_finrank_adjoin_simple_of_order hm hx hy

end Laurent2

end ModularCurve.UnitDeg

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData coeffEmb coeffEmb_mem_laurentBaseChange jqModC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence modularFunctionFieldFullC jqModC_mem_full coeff_jqModC_pow_of_lt coeff_jqModC_neg_one modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull PlaceSpecialization.LevelOneProlongationPair.order_residue_coeffEmb_modularUnitSeries finrank_adjoin_coeffEmb_modularUnitSeries_inv"
namespace UnitDeg
p2m_open "ModularCurve"

open HahnSeries

theorem order_jqModC_eq_neg_one (K : Type*) [Field K] : (jqModC K).order = -1 := by
  have h1 : (jqModC K).coeff (-1) ≠ 0 := by
    rw [coeff_jqModC_neg_one]; exact one_ne_zero
  have h0 : jqModC K ≠ 0 := fun h => h1 (by rw [h]; rfl)
  refine le_antisymm (order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  have hlt' : (jqModC K).order < -((1 : ℕ) : ℤ) := by simpa using not_le.mp hlt
  apply (coeff_order_eq_zero (x := jqModC K)).not.mpr h0
  have h := coeff_jqModC_pow_of_lt K hlt'
  rwa [pow_one] at h

theorem sub_one_le_finrank_adjoin_inv_of_order {k₀ : Type*} [Field k₀] {q : ℕ} [hq : Fact q.Prime]
    (xbar : ↥(modularFunctionFieldFullC k₀ 1))
    (hord : ((xbar : ↥(modularFunctionFieldFullC k₀ 1)) : LaurentSeries k₀).order = 1 - (q : ℤ))
    [FiniteDimensional (IntermediateField.adjoin k₀ ({xbar⁻¹} : Set ↥(modularFunctionFieldFullC k₀ 1)))
      ↥(modularFunctionFieldFullC k₀ 1)] :
    q - 1 ≤ Module.finrank (IntermediateField.adjoin k₀ ({xbar⁻¹} : Set ↥(modularFunctionFieldFullC k₀ 1)))
      ↥(modularFunctionFieldFullC k₀ 1) := by
  have hq2 : 2 ≤ q := hq.out.two_le
  have hm : 0 < q - 1 := by omega
  have hx : ((xbar : ↥(modularFunctionFieldFullC k₀ 1)) : LaurentSeries k₀).order = -((q - 1 : ℕ) : ℤ) := by
    rw [hord, Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; ring
  have hy : ((⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) :
      LaurentSeries k₀).order = -1 := order_jqModC_eq_neg_one k₀
  exact le_finrank_adjoin_simple_inv_of_order hm hx hy

end ModularCurve.UnitDeg

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData coeffEmb coeffEmb_mem_laurentBaseChange jqModC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence modularFunctionFieldFullC jqModC_mem_full coeff_jqModC_pow_of_lt coeff_jqModC_neg_one modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull PlaceSpecialization.LevelOneProlongationPair.order_residue_coeffEmb_modularUnitSeries finrank_adjoin_coeffEmb_modularUnitSeries_inv"
namespace UnitDeg
p2m_open "ModularCurve"

open AlgebraicCurve IsLocalRing in

theorem finiteDimensional_and_finrank_adjoin_residue_inv_le
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) {x : F} (h : x ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨x, h⟩))
    [hF : FiniteDimensional (IntermediateField.adjoin L ({x⁻¹} : Set F)) F] :
    FiniteDimensional
        (IntermediateField.adjoin (ResidueField A) ({(R.residue ⟨x, h⟩)⁻¹} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin (ResidueField A) ({(R.residue ⟨x, h⟩)⁻¹} : Set Fbar)) Fbar ≤
        Module.finrank (IntermediateField.adjoin L ({x⁻¹} : Set F)) F := by
  rw [adjoin_simple_inv_eq x] at hF
  rw [adjoin_simple_inv_eq (R.residue ⟨x, h⟩), adjoin_simple_inv_eq x]
  obtain ⟨hfin, hle⟩ :=
    AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le A (ι := Unit) (fun _ => Fbar)
      (fun _ => R) (fun a b _ => Subsingleton.elim a b) x (fun _ => h) (fun _ => htr)
  exact ⟨hfin (), by simpa using hle⟩

end ModularCurve.UnitDeg

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1)⁻¹} :
          Set ↥(modularFunctionFieldFullC (ResidueField A) 1)))
      ↥(modularFunctionFieldFullC (ResidueField A) 1) = q - 1 := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  have hord := PlaceSpecialization.LevelOneProlongationPair.order_residue_coeffEmb_modularUnitSeries R h

  have htr : Transcendental (ResidueField A)
      (R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :=
    UnitDeg.transcendental_of_order_coe_ne_zero (by rw [hord]; omega)

  have hgen := ModularCurve.finrank_adjoin_coeffEmb_modularUnitSeries_inv (q := q)
  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
        ↥(modularFunctionFieldBar (1 * q))))⁻¹} : Set ↥(modularFunctionFieldBar (1 * q))))
      ↥(modularFunctionFieldBar (1 * q)) :=
    Module.finite_of_finrank_pos (by rw [hgen]; omega)

  obtain ⟨hfin, hub⟩ := UnitDeg.finiteDimensional_and_finrank_adjoin_residue_inv_le R.R₁ h htr
  haveI := hfin

  exact le_antisymm (hub.trans hgen.le) (UnitDeg.sub_one_le_finrank_adjoin_inv_of_order _ hord)

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv (solution)
