-- Prove2me | solution 1 for LocalGL2.exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/32074e72-a69f-53e8-a3cd-dbe10cfa6cdc

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq

set_option autoImplicit false

open scoped Pointwise
p2m_open "LocalGL2 P2MW.S_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq.LocalGL2 HeckePair"

namespace LocalGL2
p2m_export "LocalGL2" "unipotentInt unipotentInt_mem weylInt weylInt_mem diagPi coe_diagPi localRepSome coe_localRepSome localRepInf coe_localRepInf heckeMulSet mem_heckeMulSet_iff dvd_sub_of_mk_localRepSome_eq mk_localRepSome_eq_of_dvd_sub mk_localRepSome_ne_mk_localRepInf exists_rep_of_mem_heckeMulSet finite_image_mul_diagPi integralSubgroup iwasawa_decomposition_diag"
namespace IwasawaSlice
p2m_open "LocalGL2"

private def slice {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] (ϖ : R) (a b : ℤ) :
    Set (GL (Fin 2) K ⧸ integralSubgroup R K) :=
  {c | ∃ g : GL (Fin 2) K, QuotientGroup.mk g = c ∧
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a ∧
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b}

open Classical in

private noncomputable def sliceIndex {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] (ϖ : R)
    (c : GL (Fin 2) K ⧸ integralSubgroup R K) : ℤ × ℤ :=
  if h : ∃ p : ℤ × ℤ, c ∈ slice (R := R) (K := K) ϖ p.1 p.2 then h.choose else 0

private noncomputable def ct {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] (ϖ : R)
    {R₀ : Type*} [AddCommMonoid R₀] (f : GL (Fin 2) K → R₀) (p : ℤ × ℤ) : R₀ :=
  ∑ᶠ c : GL (Fin 2) K ⧸ integralSubgroup R K,
    Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2) (fun c => f (Quotient.out c)) c

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem mem_slice_iff (ϖ : R) (a b : ℤ) (c : GL (Fin 2) K ⧸ integralSubgroup R K) :
    c ∈ slice (R := R) (K := K) ϖ a b ↔ ∃ g : GL (Fin 2) K, QuotientGroup.mk g = c ∧
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a ∧
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b :=
  Iff.rfl

private theorem inv_mul_entries {g g' : GL (Fin 2) K}
    (hg10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hg00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0)
    (hg11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0) (hg'10 : (g' : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ((g⁻¹ * g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
    ((g⁻¹ * g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (g' : Matrix (Fin 2) (Fin 2) K) 0 0 * ((g : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ ∧
    ((g⁻¹ * g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (g' : Matrix (Fin 2) (Fin 2) K) 1 1 * ((g : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹ := by
  set M : Matrix (Fin 2) (Fin 2) K := ((g⁻¹ * g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM

  have hprod : (g : Matrix (Fin 2) (Fin 2) K) * M = (g' : Matrix (Fin 2) (Fin 2) K) := by
    rw [hM, ← Units.val_mul, mul_inv_cancel_left]
  have e10 := congrFun (congrFun hprod 1) 0
  have e00 := congrFun (congrFun hprod 0) 0
  have e11 := congrFun (congrFun hprod 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg10, zero_mul, zero_add] at e10 e00 e11

  have hM10 : M 1 0 = 0 := by
    rw [hg'10] at e10
    rcases mul_eq_zero.mp e10 with h | h
    · exact absurd h hg11
    · exact h
  refine ⟨hM10, ?_, ?_⟩
  · rw [hM10, mul_zero, add_zero] at e00
    rw [← e00, mul_comm ((g : Matrix (Fin 2) (Fin 2) K) 0 0), mul_assoc, mul_inv_cancel₀ hg00, mul_one]
  · rw [← e11, mul_comm ((g : Matrix (Fin 2) (Fin 2) K) 1 1), mul_assoc, mul_inv_cancel₀ hg11, mul_one]

private theorem diag_ne_zero {g : GL (Fin 2) K} (hg10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_fin_two, hg10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

private theorem zpow_eq_unit [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ)
    (h : algebraMap R K (u : R) = algebraMap R K ϖ ^ n) : n = 0 := by
  have hinj := IsFractionRing.injective R K
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  ·
    rw [zpow_natCast, ← map_pow] at h
    have hu : IsUnit (ϖ ^ m) := by rw [← hinj h]; exact u.isUnit
    have hm : m = 0 := (isUnit_pow_iff_of_not_isUnit hϖ.not_isUnit).mp hu
    rw [hm, Nat.cast_zero]
  ·
    rw [zpow_neg, zpow_natCast, ← map_pow] at h
    have hϖm0 : algebraMap R K (ϖ ^ m) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hϖ.ne_zero)
    have h1 : algebraMap R K ((u : R) * ϖ ^ m) = algebraMap R K 1 := by
      rw [map_mul, map_one, h, inv_mul_cancel₀ hϖm0]
    have h2 : ϖ ^ m * (u : R) = 1 := by rw [mul_comm]; exact hinj h1
    have hu : IsUnit (ϖ ^ m) := IsUnit.of_mul_eq_one _ h2
    have hm : m = 0 := (isUnit_pow_iff_of_not_isUnit hϖ.not_isUnit).mp hu
    rw [hm, Nat.cast_zero, neg_zero]

private theorem slice_disjoint [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {a b a' b' : ℤ}
    {c : GL (Fin 2) K ⧸ integralSubgroup R K}
    (h : c ∈ slice (R := R) (K := K) ϖ a b) (h' : c ∈ slice (R := R) (K := K) ϖ a' b') :
    a = a' ∧ b = b' := by
  have hinj := IsFractionRing.injective R K
  have hπ : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  obtain ⟨g, hgc, hg10, hg00, hg11⟩ := h
  obtain ⟨g', hg'c, hg'10, hg'00, hg'11⟩ := h'

  have hmem : g⁻¹ * g' ∈ integralSubgroup R K := by
    rw [← QuotientGroup.eq, hgc, hg'c]
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨hne00, hne11⟩ := diag_ne_zero (K := K) hg10
  obtain ⟨hM10, hM00, hM11⟩ := inv_mul_entries (K := K) hg10 hne00 hne11 hg'10

  have hyij : ∀ i j, algebraMap R K ((y : Matrix (Fin 2) (Fin 2) R) i j) =
      ((g⁻¹ * g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j
    rw [← hy]
    rfl
  have hy10 : (y : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
    apply hinj
    rw [hyij, hM10, map_zero]

  have hdet : IsUnit ((y : Matrix (Fin 2) (Fin 2) R) 0 0 * (y : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
    rw [Matrix.det_fin_two, hy10, mul_zero, sub_zero] at this
    exact this
  obtain ⟨hu00, hu11⟩ := IsUnit.mul_iff.mp hdet
  obtain ⟨u₀, hu₀⟩ := hu00
  obtain ⟨u₁, hu₁⟩ := hu11

  have h00 : algebraMap R K (u₀ : R) = algebraMap R K ϖ ^ (a' - a) := by
    rw [hu₀, hyij, hM00, hg'00, hg00, zpow_sub₀ hπ, div_eq_mul_inv]
  have h11 : algebraMap R K (u₁ : R) = algebraMap R K ϖ ^ (b' - b) := by
    rw [hu₁, hyij, hM11, hg'11, hg11, zpow_sub₀ hπ, div_eq_mul_inv]
  have ha := zpow_eq_unit (K := K) hϖ u₀ (a' - a) h00
  have hb := zpow_eq_unit (K := K) hϖ u₁ (b' - b) h11
  constructor <;> omega

private theorem inv_smul_mem_slice [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {a₁ b₁ a b : ℤ} {δ : GL (Fin 2) K}
    (hδ10 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hδ00 : (δ : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a₁)
    (hδ11 : (δ : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b₁)
    {c : GL (Fin 2) K ⧸ integralSubgroup R K} (hc : c ∈ slice (R := R) (K := K) ϖ a b) :
    δ⁻¹ • c ∈ slice (R := R) (K := K) ϖ (a - a₁) (b - b₁) := by
  have hinj := IsFractionRing.injective R K
  have hπ : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  obtain ⟨g, hgc, hg10, hg00, hg11⟩ := hc
  have hne00 : (δ : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by rw [hδ00]; exact zpow_ne_zero _ hπ
  have hne11 : (δ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by rw [hδ11]; exact zpow_ne_zero _ hπ
  obtain ⟨hM10, hM00, hM11⟩ := inv_mul_entries (K := K) hδ10 hne00 hne11 hg10
  refine ⟨δ⁻¹ * g, ?_, hM10, ?_, ?_⟩
  · rw [← hgc]
    rfl
  · rw [hM00, hg00, hδ00, zpow_sub₀ hπ, div_eq_mul_inv]
  · rw [hM11, hg11, hδ11, zpow_sub₀ hπ, div_eq_mul_inv]

private theorem inv_entries [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {a₁ b₁ : ℤ} {δ : GL (Fin 2) K}
    (hδ10 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hδ00 : (δ : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a₁)
    (hδ11 : (δ : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b₁) :
    ((δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
    ((δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ (-a₁) ∧
    ((δ⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ (-b₁) := by
  have hinj := IsFractionRing.injective R K
  have hπ : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hne00 : (δ : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by rw [hδ00]; exact zpow_ne_zero _ hπ
  have hne11 : (δ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by rw [hδ11]; exact zpow_ne_zero _ hπ
  have h1 : ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp
  obtain ⟨hM10, hM00, hM11⟩ := inv_mul_entries (K := K) hδ10 hne00 hne11 h1
  rw [mul_one] at hM10 hM00 hM11
  refine ⟨hM10, ?_, ?_⟩
  · rw [hM00, Units.val_one, Matrix.one_apply_eq, one_mul, hδ00, zpow_neg]
  · rw [hM11, Units.val_one, Matrix.one_apply_eq, one_mul, hδ11, zpow_neg]

private theorem inv_smul_mem_slice_iff [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {a₁ b₁ a b : ℤ} {δ : GL (Fin 2) K}
    (hδ10 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (hδ00 : (δ : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a₁)
    (hδ11 : (δ : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b₁)
    (c : GL (Fin 2) K ⧸ integralSubgroup R K) :
    δ⁻¹ • c ∈ slice (R := R) (K := K) ϖ (a - a₁) (b - b₁) ↔ c ∈ slice (R := R) (K := K) ϖ a b := by
  constructor
  · intro h
    obtain ⟨hi10, hi00, hi11⟩ := inv_entries (K := K) hϖ hδ10 hδ00 hδ11
    have := inv_smul_mem_slice (K := K) hϖ hi10 hi00 hi11 h
    rw [inv_inv, smul_inv_smul] at this
    simpa only [sub_neg_eq_add, sub_add_cancel] using this
  · exact inv_smul_mem_slice (K := K) hϖ hδ10 hδ00 hδ11

private theorem exists_zpow_mul_unit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Rˣ), x = algebraMap R K ϖ ^ n * algebraMap R K (u : R) := by
  have hinj := IsFractionRing.injective R K
  have hπ : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hrs
    exact hx hrs.symm
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  refine ⟨(m : ℤ) - n, u * v⁻¹, ?_⟩
  rw [← hrs, map_mul, map_mul, map_pow, map_pow, Units.val_mul, map_mul, map_units_inv, zpow_sub₀ hπ,
    zpow_natCast, zpow_natCast, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

private theorem exists_mem_slice [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (c : GL (Fin 2) K ⧸ integralSubgroup R K) :
    ∃ a b : ℤ, c ∈ slice (R := R) (K := K) ϖ a b := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨z, a₁, a₂, k, hk, hg⟩ := LocalGL2.iwasawa_decomposition_diag R K g
  have hinj := IsFractionRing.injective R K
  obtain ⟨n₁, u₁, hu₁⟩ := exists_zpow_mul_unit (K := K) hϖ a₁.ne_zero
  obtain ⟨n₂, u₂, hu₂⟩ := exists_zpow_mul_unit (K := K) hϖ a₂.ne_zero
  have hιu₁ : algebraMap R K (u₁ : R) ≠ 0 := (map_ne_zero_iff _ hinj).mpr u₁.ne_zero
  have hιu₂ : algebraMap R K (u₂ : R) ≠ 0 := (map_ne_zero_iff _ hinj).mpr u₂.ne_zero

  let dR : GL (Fin 2) R :=
    ⟨!![((u₁⁻¹ : Rˣ) : R), 0; 0, ((u₂⁻¹ : Rˣ) : R)], !![(u₁ : R), 0; 0, (u₂ : R)],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  have hdR : (dR : Matrix (Fin 2) (Fin 2) R) = !![((u₁⁻¹ : Rˣ) : R), 0; 0, ((u₂⁻¹ : Rˣ) : R)] := rfl
  let D : GL (Fin 2) K := Matrix.GeneralLinearGroup.map (algebraMap R K) dR
  have hDmem : D ∈ integralSubgroup R K := ⟨dR, rfl⟩
  have hDij : ∀ i j, (D : Matrix (Fin 2) (Fin 2) K) i j =
      algebraMap R K ((dR : Matrix (Fin 2) (Fin 2) R) i j) := fun i j => rfl
  have hDmat : (D : Matrix (Fin 2) (Fin 2) K) =
      !![(algebraMap R K (u₁ : R))⁻¹, 0; 0, (algebraMap R K (u₂ : R))⁻¹] := by
    ext i j
    rw [hDij, hdR]
    fin_cases i <;> fin_cases j <;> simp [map_units_inv]

  have hval : ((g * k⁻¹ * D : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(1 : K), z; 0, 1] * !![(a₁ : K), 0; 0, (a₂ : K)] * (D : Matrix (Fin 2) (Fin 2) K) := by
    rw [Units.val_mul, Units.val_mul, hg, mul_assoc _ (k : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one]
  refine ⟨n₁, n₂, g * k⁻¹ * D, ?_, ?_, ?_, ?_⟩
  ·
    rw [QuotientGroup.eq]
    have hw : (g * k⁻¹ * D)⁻¹ * g = D⁻¹ * k := by group
    rw [hw]
    exact mul_mem (inv_mem hDmem) hk
  · rw [hval, hDmat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp
  · rw [hval, hDmat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp [hu₁]
  · rw [hval, hDmat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp [hu₂]

private theorem sliceIndex_eq [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {c : GL (Fin 2) K ⧸ integralSubgroup R K} {p : ℤ × ℤ}
    (hc : c ∈ slice (R := R) (K := K) ϖ p.1 p.2) : sliceIndex (R := R) (K := K) ϖ c = p := by
  classical
  have h : ∃ p : ℤ × ℤ, c ∈ slice (R := R) (K := K) ϖ p.1 p.2 := ⟨p, hc⟩
  have hspec := h.choose_spec
  obtain ⟨h1, h2⟩ := slice_disjoint (K := K) hϖ hspec hc
  unfold sliceIndex
  rw [dif_pos h]
  exact Prod.ext h1 h2

private theorem finite_sliceSupport [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {R₀ : Type*} [Zero R₀]
    {f : GL (Fin 2) K → R₀}
    (hf : ((QuotientGroup.mk '' Function.support f) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    {p : ℤ × ℤ | ∃ c ∈ slice (R := R) (K := K) ϖ p.1 p.2, f (Quotient.out c) ≠ 0}.Finite := by
  refine (hf.image (sliceIndex (R := R) (K := K) ϖ)).subset ?_
  rintro p ⟨c, hc, hfc⟩
  refine ⟨c, ⟨Quotient.out c, Function.mem_support.mpr hfc, QuotientGroup.out_eq' c⟩, ?_⟩
  exact sliceIndex_eq (K := K) hϖ hc

private theorem finite_support_indicator (ϖ : R) (a b : ℤ) {R₀ : Type*} [Zero R₀] {f : GL (Fin 2) K → R₀}
    (hf : ((QuotientGroup.mk '' Function.support f) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    (Function.support (Set.indicator (slice (R := R) (K := K) ϖ a b)
      (fun c => f (Quotient.out c)))).Finite := by
  classical
  refine hf.subset ?_
  intro c hc
  rw [Function.mem_support] at hc
  have hfc : f (Quotient.out c) ≠ 0 := fun h => hc (Set.indicator_apply_eq_zero.mpr fun _ => h)
  exact ⟨Quotient.out c, Function.mem_support.mpr hfc, QuotientGroup.out_eq' c⟩

section HeckeAlgebra

variable {R₀ : Type*} [CommRing R₀]

private theorem ct_eq_sum (ϖ : R) (f : HeckeAlgebra (integralSubgroup R K) R₀) (p : ℤ × ℤ)
    {T : Finset (GL (Fin 2) K ⧸ integralSubgroup R K)}
    (hT : QuotientGroup.mk '' Function.support (f : GL (Fin 2) K → R₀) ⊆
      (T : Set (GL (Fin 2) K ⧸ integralSubgroup R K))) :
    ct (R := R) (K := K) ϖ (f : GL (Fin 2) K → R₀) p =
      ∑ c ∈ T, Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
        (fun c => (f : GL (Fin 2) K → R₀) (Quotient.out c)) c := by
  classical
  unfold ct
  refine finsum_eq_sum_of_support_subset _ ?_
  intro c hc
  rw [Function.mem_support] at hc
  have hfc : (f : GL (Fin 2) K → R₀) (Quotient.out c) ≠ 0 :=
    fun h => hc (Set.indicator_apply_eq_zero.mpr fun _ => h)
  exact hT ⟨Quotient.out c, Function.mem_support.mpr hfc, QuotientGroup.out_eq' c⟩

private theorem ct_add (ϖ : R) (f g : HeckeAlgebra (integralSubgroup R K) R₀) (p : ℤ × ℤ) :
    ct (R := R) (K := K) ϖ ((f + g : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
      ct (R := R) (K := K) ϖ (f : GL (Fin 2) K → R₀) p + ct (R := R) (K := K) ϖ (g : GL (Fin 2) K → R₀) p := by
  classical
  unfold ct
  rw [← finsum_add_distrib (finite_support_indicator (R := R) ϖ p.1 p.2 (finite_cosets f))
    (finite_support_indicator (R := R) ϖ p.1 p.2 (finite_cosets g))]
  refine finsum_congr fun c => ?_
  simp only [Set.indicator_apply, coe_apply_add]
  split_ifs <;> simp

private theorem ct_smul (ϖ : R) (r : R₀) (f : HeckeAlgebra (integralSubgroup R K) R₀) (p : ℤ × ℤ) :
    ct (R := R) (K := K) ϖ ((r • f : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
      r * ct (R := R) (K := K) ϖ (f : GL (Fin 2) K → R₀) p := by
  classical
  unfold ct
  rw [mul_finsum' _ _ (finite_support_indicator (R := R) ϖ p.1 p.2 (finite_cosets f))]
  refine finsum_congr fun c => ?_
  simp only [Set.indicator_apply, coe_apply_smul]
  split_ifs <;> simp

private theorem mk_one_mem_slice_iff [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (a b : ℤ) :
    (QuotientGroup.mk (1 : GL (Fin 2) K) : GL (Fin 2) K ⧸ integralSubgroup R K) ∈
        slice (R := R) (K := K) ϖ a b ↔ a = 0 ∧ b = 0 := by
  have h0 : (QuotientGroup.mk (1 : GL (Fin 2) K) : GL (Fin 2) K ⧸ integralSubgroup R K) ∈
      slice (R := R) (K := K) ϖ 0 0 :=
    ⟨1, rfl, by simp, by simp, by simp⟩
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := slice_disjoint (K := K) hϖ h h0
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    exact h0

private theorem ct_one [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (p : ℤ × ℤ) :
    ct (R := R) (K := K) ϖ ((1 : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
      if p = 0 then 1 else 0 := by
  classical
  unfold ct

  rw [finsum_eq_single _ (QuotientGroup.mk (1 : GL (Fin 2) K))]
  · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) (1 : GL (Fin 2) K)
    have hval : ((1 : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀)
        (Quotient.out (QuotientGroup.mk (1 : GL (Fin 2) K) : GL (Fin 2) K ⧸ integralSubgroup R K)) = 1 := by
      rw [hu, one_mul]
      exact one_apply_of_mem u.2
    rw [Set.indicator_apply, hval]
    by_cases hmem : (QuotientGroup.mk (1 : GL (Fin 2) K) : GL (Fin 2) K ⧸ integralSubgroup R K) ∈
        slice (R := R) (K := K) ϖ p.1 p.2
    · obtain ⟨h1, h2⟩ := (mk_one_mem_slice_iff (K := K) hϖ p.1 p.2).mp hmem
      have hp : p = 0 := Prod.ext h1 h2
      rw [if_pos hmem, if_pos hp]
    · have hp : p ≠ 0 := by
        rintro rfl
        exact hmem ((mk_one_mem_slice_iff (K := K) hϖ _ _).mpr ⟨rfl, rfl⟩)
      rw [if_neg hmem, if_neg hp]
  · intro c hc
    rw [Set.indicator_apply_eq_zero]
    intro _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) y
    rw [hu, apply_mul_right _ u.2]
    apply one_apply_of_notMem
    intro hy
    exact hc (QuotientGroup.eq.mpr (by simpa using inv_mem hy))

private theorem mem_slice_sliceIndex [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (d : GL (Fin 2) K ⧸ integralSubgroup R K) :
    d ∈ slice (R := R) (K := K) ϖ (sliceIndex (R := R) (K := K) ϖ d).1 (sliceIndex (R := R) (K := K) ϖ d).2 := by
  obtain ⟨a, b, hab⟩ := exists_mem_slice (K := K) hϖ d
  have hidx := sliceIndex_eq (K := K) hϖ (p := (a, b)) hab
  rw [hidx]
  exact hab

private theorem finsum_indicator_translate [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ)
    (f₂ : HeckeAlgebra (integralSubgroup R K) R₀) (d : GL (Fin 2) K ⧸ integralSubgroup R K) (p : ℤ × ℤ) :
    ∑ᶠ c : GL (Fin 2) K ⧸ integralSubgroup R K,
        Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
          (fun c => (f₂ : GL (Fin 2) K → R₀) ((Quotient.out d)⁻¹ * Quotient.out c)) c =
      ct (R := R) (K := K) ϖ (f₂ : GL (Fin 2) K → R₀) (p - sliceIndex (R := R) (K := K) ϖ d) := by
  classical
  set p₁ := sliceIndex (R := R) (K := K) ϖ d with hp₁

  obtain ⟨δ, hδd, hδ10, hδ00, hδ11⟩ := mem_slice_sliceIndex (K := K) hϖ d
  rw [← hp₁] at hδ00 hδ11

  obtain ⟨u, hu⟩ : ∃ u : integralSubgroup R K, Quotient.out d = δ * u := by
    rw [← hδd]
    exact QuotientGroup.mk_out_eq_mul (integralSubgroup R K) δ
  have hrep : ∀ c : GL (Fin 2) K ⧸ integralSubgroup R K,
      (f₂ : GL (Fin 2) K → R₀) ((Quotient.out d)⁻¹ * Quotient.out c) =
        (f₂ : GL (Fin 2) K → R₀) (Quotient.out (δ⁻¹ • c)) := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) y
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) (δ⁻¹ * y)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, hv, hw, hu, mul_inv_rev]
    have harg : ((u : GL (Fin 2) K))⁻¹ * δ⁻¹ * (y * (v : GL (Fin 2) K)) =
        ((u : GL (Fin 2) K))⁻¹ * (δ⁻¹ * y * (v : GL (Fin 2) K)) := by group
    rw [harg, apply_left_mul _ (inv_mem u.2), apply_mul_right _ v.2, apply_mul_right _ w.2]
  calc ∑ᶠ c : GL (Fin 2) K ⧸ integralSubgroup R K, Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
          (fun c => (f₂ : GL (Fin 2) K → R₀) ((Quotient.out d)⁻¹ * Quotient.out c)) c
      = ∑ᶠ c : GL (Fin 2) K ⧸ integralSubgroup R K,
          Set.indicator (slice (R := R) (K := K) ϖ (p - p₁).1 (p - p₁).2)
            (fun e => (f₂ : GL (Fin 2) K → R₀) (Quotient.out e)) ((MulAction.toPerm δ⁻¹) c) := by
        refine finsum_congr fun c => ?_
        rw [MulAction.toPerm_apply, Set.indicator_apply, Set.indicator_apply, hrep c]
        refine if_congr ?_ rfl rfl
        rw [Prod.fst_sub, Prod.snd_sub]
        exact (inv_smul_mem_slice_iff (K := K) hϖ hδ10 hδ00 hδ11 c).symm
    _ = ∑ᶠ e : GL (Fin 2) K ⧸ integralSubgroup R K,
          Set.indicator (slice (R := R) (K := K) ϖ (p - p₁).1 (p - p₁).2)
            (fun e => (f₂ : GL (Fin 2) K → R₀) (Quotient.out e)) e :=
        finsum_comp_equiv (MulAction.toPerm δ⁻¹)
    _ = ct (R := R) (K := K) ϖ (f₂ : GL (Fin 2) K → R₀) (p - p₁) := rfl

private theorem ct_mul [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (f₁ f₂ : HeckeAlgebra (integralSubgroup R K) R₀) (p : ℤ × ℤ) :
    ct (R := R) (K := K) ϖ ((f₁ * f₂ : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
      ∑ p₁ ∈ (finite_cosets f₁).toFinset.image (sliceIndex (R := R) (K := K) ϖ),
        ct (R := R) (K := K) ϖ (f₁ : GL (Fin 2) K → R₀) p₁ *
          ct (R := R) (K := K) ϖ (f₂ : GL (Fin 2) K → R₀) (p - p₁) := by
  classical
  set D₁ : Finset (GL (Fin 2) K ⧸ integralSubgroup R K) := (finite_cosets f₁).toFinset with hD₁
  set C : Finset (GL (Fin 2) K ⧸ integralSubgroup R K) := (finite_image_mk_mul_support f₁ f₂).toFinset with hC
  have hD₁sub : QuotientGroup.mk '' Function.support (f₁ : GL (Fin 2) K → R₀) ⊆
      (D₁ : Set (GL (Fin 2) K ⧸ integralSubgroup R K)) := by
    intro c hc
    rw [hD₁, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hc
  have hCsub : QuotientGroup.mk '' Function.support
      ((f₁ * f₂ : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) ⊆
      (C : Set (GL (Fin 2) K ⧸ integralSubgroup R K)) := by
    intro c hc
    rw [hC, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact Set.image_mono (support_conv_subset f₁ f₂) hc

  have hD₁out : ∀ d ∈ D₁, (f₁ : GL (Fin 2) K → R₀) (Quotient.out d) ≠ 0 := by
    intro d hd
    rw [hD₁, Set.Finite.mem_toFinset] at hd
    obtain ⟨y, hy, rfl⟩ := hd
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) y
    rw [hv, apply_mul_right _ v.2]
    exact Function.mem_support.mp hy

  have step1 : ct (R := R) (K := K) ϖ ((f₁ * f₂ : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p
      = ∑ d ∈ D₁, (f₁ : GL (Fin 2) K → R₀) (Quotient.out d) *
          ∑ c ∈ C, Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
            (fun c => (f₂ : GL (Fin 2) K → R₀) ((Quotient.out d)⁻¹ * Quotient.out c)) c := by
    rw [ct_eq_sum (R := R) ϖ (f₁ * f₂) p hCsub]
    have hterm : ∀ c ∈ C, Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
        (fun c => ((f₁ * f₂ : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) (Quotient.out c)) c
        = ∑ d ∈ D₁, (f₁ : GL (Fin 2) K → R₀) (Quotient.out d) *
            Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
              (fun c => (f₂ : GL (Fin 2) K → R₀) ((Quotient.out d)⁻¹ * Quotient.out c)) c := by
      intro c _
      rw [coe_mul, Set.indicator_apply]
      split_ifs with hc
      · rw [conv_eq_sum f₁ f₂ (Quotient.out c) hD₁sub]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Set.indicator_of_mem hc]
        conv_lhs => rw [← QuotientGroup.out_eq' d]
        rw [convTerm_mk]
      · symm
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [Set.indicator_of_notMem hc, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]

  have step2 : ∀ d ∈ D₁, ∑ c ∈ C, Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
        (fun c => (f₂ : GL (Fin 2) K → R₀) ((Quotient.out d)⁻¹ * Quotient.out c)) c
      = ct (R := R) (K := K) ϖ (f₂ : GL (Fin 2) K → R₀) (p - sliceIndex (R := R) (K := K) ϖ d) := by
    intro d hd
    rw [← finsum_indicator_translate (K := K) hϖ f₂ d p]
    symm
    refine finsum_eq_sum_of_support_subset _ ?_
    intro c hc
    rw [Function.mem_support] at hc
    have hfc : (f₂ : GL (Fin 2) K → R₀) ((Quotient.out d)⁻¹ * Quotient.out c) ≠ 0 :=
      fun h => hc (Set.indicator_apply_eq_zero.mpr fun _ => h)
    rw [Finset.mem_coe, hC, Set.Finite.mem_toFinset]
    refine ⟨Quotient.out c, ⟨Quotient.out d, Function.mem_support.mpr (hD₁out d hd),
      (Quotient.out d)⁻¹ * Quotient.out c, Function.mem_support.mpr hfc, by group⟩, QuotientGroup.out_eq' c⟩

  have step3 : ∀ p₁ : ℤ × ℤ, ∑ d ∈ D₁ with sliceIndex (R := R) (K := K) ϖ d = p₁,
        (f₁ : GL (Fin 2) K → R₀) (Quotient.out d)
      = ct (R := R) (K := K) ϖ (f₁ : GL (Fin 2) K → R₀) p₁ := by
    intro p₁
    rw [ct_eq_sum (R := R) ϖ f₁ p₁ hD₁sub, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Set.indicator_apply]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro rfl
      exact mem_slice_sliceIndex (K := K) hϖ d
    · intro hd
      exact sliceIndex_eq (K := K) hϖ (p := p₁) hd

  rw [step1, ← Finset.sum_fiberwise_of_maps_to (g := sliceIndex (R := R) (K := K) ϖ)
    (t := D₁.image (sliceIndex (R := R) (K := K) ϖ)) (fun d hd => Finset.mem_image_of_mem _ hd)]
  refine Finset.sum_congr rfl fun p₁ _ => ?_
  rw [← step3 p₁, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_filter] at hd
  rw [step2 d hd.1, hd.2]

end HeckeAlgebra

section AlgHom

variable {R₀ : Type*} [CommRing R₀]

private theorem finite_support_ct [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (f : HeckeAlgebra (integralSubgroup R K) R₀) :
    (Function.support (ct (R := R) (K := K) ϖ (f : GL (Fin 2) K → R₀))).Finite := by
  classical
  refine (finite_sliceSupport (K := K) hϖ (finite_cosets f)).subset ?_
  intro p hp
  rw [Function.mem_support] at hp
  by_contra h
  apply hp
  unfold ct
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  rw [Set.indicator_apply_eq_zero]
  intro hc
  by_contra hfc
  exact h ⟨c, hc, hfc⟩

private noncomputable def ctLinear [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) :
    HeckeAlgebra (integralSubgroup R K) R₀ →ₗ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ) where
  toFun f := .ofCoeff (Finsupp.ofSupportFinite (ct (R := R) (K := K) ϖ (f : GL (Fin 2) K → R₀))
    (finite_support_ct (K := K) hϖ f))
  map_add' f g := AddMonoidAlgebra.ext <| Finsupp.ext fun p => ct_add (R := R) (K := K) ϖ f g p
  map_smul' r f := AddMonoidAlgebra.ext <| Finsupp.ext fun p => ct_smul (R := R) (K := K) ϖ r f p

private theorem ctLinear_apply [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (f : HeckeAlgebra (integralSubgroup R K) R₀)
    (p : ℤ × ℤ) : (ctLinear (K := K) (R₀ := R₀) hϖ f).coeff p = ct (R := R) (K := K) ϖ (f : GL (Fin 2) K → R₀) p :=
  rfl

private theorem ctLinear_one [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) :
    ctLinear (K := K) (R₀ := R₀) hϖ 1 = 1 := by
  refine AddMonoidAlgebra.ext <| Finsupp.ext fun p => ?_
  change ct (R := R) (K := K) ϖ ((1 : HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
    Finsupp.single (0 : ℤ × ℤ) (1 : R₀) p
  rw [ct_one (K := K) hϖ p, Finsupp.single_apply]
  by_cases hp : p = 0
  · rw [if_pos hp, if_pos hp.symm]
  · rw [if_neg hp, if_neg (Ne.symm hp)]

private theorem ctLinear_mul [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (f₁ f₂ : HeckeAlgebra (integralSubgroup R K) R₀) :
    ctLinear (K := K) (R₀ := R₀) hϖ (f₁ * f₂) = ctLinear (K := K) hϖ f₁ * ctLinear (K := K) hϖ f₂ := by
  classical
  refine AddMonoidAlgebra.ext <| Finsupp.ext fun p => ?_
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, ctLinear_apply, ct_mul (K := K) hϖ f₁ f₂ p]
  symm
  calc ∑ p₁ ∈ (ctLinear (K := K) (R₀ := R₀) hϖ f₁).coeff.support,
        (ctLinear (K := K) (R₀ := R₀) hϖ f₁).coeff p₁ * (ctLinear (K := K) (R₀ := R₀) hϖ f₂).coeff (-p₁ + p)
      = ∑ p₁ ∈ (ctLinear (K := K) (R₀ := R₀) hϖ f₁).coeff.support,
          ct (R := R) (K := K) ϖ (f₁ : GL (Fin 2) K → R₀) p₁ *
            ct (R := R) (K := K) ϖ (f₂ : GL (Fin 2) K → R₀) (p - p₁) := by
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [neg_add_eq_sub, ctLinear_apply, ctLinear_apply]
    _ = ∑ p₁ ∈ (finite_cosets f₁).toFinset.image (sliceIndex (R := R) (K := K) ϖ),
          ct (R := R) (K := K) ϖ (f₁ : GL (Fin 2) K → R₀) p₁ *
            ct (R := R) (K := K) ϖ (f₂ : GL (Fin 2) K → R₀) (p - p₁) := by
        refine Finset.sum_subset ?_ ?_
        · intro p₁ hp₁
          rw [Finsupp.mem_support_iff, ctLinear_apply] at hp₁
          obtain ⟨c, hc⟩ : ∃ c, Set.indicator (slice (R := R) (K := K) ϖ p₁.1 p₁.2)
              (fun c => (f₁ : GL (Fin 2) K → R₀) (Quotient.out c)) c ≠ 0 := by
            by_contra h
            push Not at h
            exact hp₁ (finsum_eq_zero_of_forall_eq_zero h)
          obtain ⟨hcs, hcf⟩ := Set.indicator_apply_ne_zero.mp hc
          refine Finset.mem_image.mpr ⟨c, ?_, sliceIndex_eq (K := K) hϖ hcs⟩
          rw [Set.Finite.mem_toFinset]
          exact ⟨Quotient.out c, hcf, QuotientGroup.out_eq' c⟩
        · intro p₁ _ hp₁
          rw [Finsupp.notMem_support_iff, ctLinear_apply] at hp₁
          rw [hp₁, zero_mul]

private noncomputable def ctAlgHom [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ) :=
  AlgHom.ofLinearMap (ctLinear (K := K) hϖ) (ctLinear_one (K := K) hϖ) (ctLinear_mul (K := K) hϖ)

private theorem ctAlgHom_apply [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) (f : HeckeAlgebra (integralSubgroup R K) R₀)
    (p : ℤ × ℤ) : (ctAlgHom (K := K) (R₀ := R₀) hϖ f).coeff p = ct (R := R) (K := K) ϖ (f : GL (Fin 2) K → R₀) p :=
  rfl

end AlgHom

section Generators

variable {R₀ : Type*} [CommRing R₀]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

private theorem mk_localRepSome_mem_slice (b : R) :
    (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : GL (Fin 2) K ⧸ integralSubgroup R K) ∈
      slice (R := R) (K := K) ϖ 1 0 :=
  ⟨localRepSome ϖ hϖ0 b, rfl, by simp [coe_localRepSome], by simp [coe_localRepSome], by simp [coe_localRepSome]⟩

private theorem mk_localRepInf_mem_slice :
    (QuotientGroup.mk (localRepInf ϖ hϖ0) : GL (Fin 2) K ⧸ integralSubgroup R K) ∈
      slice (R := R) (K := K) ϖ 0 1 :=
  ⟨localRepInf ϖ hϖ0, rfl, by simp [coe_localRepInf], by simp [coe_localRepInf], by simp [coe_localRepInf]⟩

private theorem coe_diagPi_mul_localRepInf :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![algebraMap R K ϖ, 0; 0, algebraMap R K ϖ] := by
  rw [Units.val_mul, coe_diagPi, coe_localRepInf, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem mk_diagPi_mul_localRepInf_mem_slice :
    (QuotientGroup.mk (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) : GL (Fin 2) K ⧸ integralSubgroup R K) ∈
      slice (R := R) (K := K) ϖ 1 1 :=
  ⟨diagPi ϖ hϖ0 * localRepInf ϖ hϖ0, rfl, by simp, by simp [Algebra.algebraMap_eq_smul_one], by simp⟩

private theorem mul_diagPi_mul_localRepInf_comm (g : GL (Fin 2) K) :
    g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0), coe_diagPi_mul_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem ct_heckeIndicator_diagPi [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (p : ℤ × ℤ) :
    ct (R := R) (K := K) ϖ ((heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ) :
        HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
      (if ((1, 0) : ℤ × ℤ) = p then (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) else 0) +
        (if ((0, 1) : ℤ × ℤ) = p then (1 : R₀) else 0) := by
  classical
  haveI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  set T : HeckeAlgebra (integralSubgroup R K) R₀ :=
    heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)

  set ψ : R ⧸ Ideal.span {ϖ} → GL (Fin 2) K ⧸ integralSubgroup R K :=
    fun r => QuotientGroup.mk (localRepSome ϖ hϖ0 (Quotient.out r))
  set cInf : GL (Fin 2) K ⧸ integralSubgroup R K := QuotientGroup.mk (localRepInf ϖ hϖ0) with hcInf
  have hψinj : Function.Injective ψ := by
    intro r r' h
    have hdvd := dvd_sub_of_mk_localRepSome_eq ϖ hϖ0 h
    rw [← Ideal.Quotient.mk_out r, ← Ideal.Quotient.mk_out r']
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (dvd_sub_comm.mp hdvd))
  have hψb : ∀ b : R, (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : GL (Fin 2) K ⧸ integralSubgroup R K) =
      ψ (Ideal.Quotient.mk (Ideal.span {ϖ}) b) := by
    intro b
    show (QuotientGroup.mk (localRepSome ϖ hϖ0 b) : GL (Fin 2) K ⧸ integralSubgroup R K) =
      QuotientGroup.mk (localRepSome ϖ hϖ0 (Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) b)))
    refine mk_localRepSome_eq_of_dvd_sub ϖ hϖ0 (Ideal.mem_span_singleton.mp ?_)
    rw [← Ideal.Quotient.eq]
    exact Ideal.Quotient.mk_out _
  have hne : ∀ r, ψ r ≠ cInf := fun r => mk_localRepSome_ne_mk_localRepInf ϖ hϖ0 hϖ.not_isUnit _

  set TF : Finset (GL (Fin 2) K ⧸ integralSubgroup R K) := Finset.univ.image ψ ∪ {cInf} with hTF
  have hdisj : Disjoint (Finset.univ.image ψ) ({cInf} : Finset _) := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨r, _, hr⟩
    exact hne r hr
  have hsupp : QuotientGroup.mk '' Function.support (T : GL (Fin 2) K → R₀) ⊆
      (TF : Set (GL (Fin 2) K ⧸ integralSubgroup R K)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxD : x ∈ doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0) := by
      by_contra hxD
      exact hx (heckeIndicator_apply_of_notMem _ hxD)
    have hxM : (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K) ∈
        QuotientGroup.mk '' heckeMulSet ϖ hϖ0 := by
      show _ ∈ QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {diagPi ϖ hϖ0})
      rw [← image_mk_doubleCoset]
      exact ⟨x, hxD, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hxM
    rw [Finset.mem_coe, hTF, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    rcases exists_rep_of_mem_heckeMulSet ϖ hϖ0 hϖ hy with ⟨b, hb⟩ | hinf
    · left
      refine ⟨Ideal.Quotient.mk (Ideal.span {ϖ}) b, Finset.mem_univ _, ?_⟩
      rw [← hψb, hb, hyx]
    · right
      exact (hcInf.trans (hinf.trans hyx)).symm

  have hval : ∀ x : GL (Fin 2) K, x ∈ heckeMulSet ϖ hϖ0 →
      (T : GL (Fin 2) K → R₀) (Quotient.out (QuotientGroup.mk x : GL (Fin 2) K ⧸ integralSubgroup R K)) = 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (mem_heckeMulSet_iff ϖ hϖ0).mp hx
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) (u * diagPi ϖ hϖ0)
    rw [hv]
    exact heckeIndicator_apply_of_mem _ (mem_doubleCoset_iff.mpr ⟨u, hu, v, v.2, rfl⟩)
  have hvalψ : ∀ r, (T : GL (Fin 2) K → R₀) (Quotient.out (ψ r)) = 1 := fun r =>
    hval _ ((mem_heckeMulSet_iff ϖ hϖ0).mpr ⟨unipotentInt K (Quotient.out r), unipotentInt_mem _, rfl⟩)
  have hvalInf : (T : GL (Fin 2) K → R₀) (Quotient.out cInf) = 1 := by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) (localRepInf ϖ hϖ0)
    rw [hcInf, hv]
    refine heckeIndicator_apply_of_mem _ (mem_doubleCoset_iff.mpr ⟨weylInt R K, weylInt_mem,
      weylInt R K * (v : GL (Fin 2) K), mul_mem weylInt_mem v.2, ?_⟩)
    show weylInt R K * diagPi ϖ hϖ0 * (weylInt R K * (v : GL (Fin 2) K)) =
      weylInt R K * diagPi ϖ hϖ0 * weylInt R K * (v : GL (Fin 2) K)
    rw [← mul_assoc]

  have hmemψ : ∀ r, ψ r ∈ slice (R := R) (K := K) ϖ p.1 p.2 ↔ ((1, 0) : ℤ × ℤ) = p := by
    intro r
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := slice_disjoint (K := K) hϖ (mk_localRepSome_mem_slice (K := K) ϖ hϖ0 _) h
      exact Prod.ext h1 h2
    · rintro rfl
      exact mk_localRepSome_mem_slice (K := K) ϖ hϖ0 _
  have hmemInf : cInf ∈ slice (R := R) (K := K) ϖ p.1 p.2 ↔ ((0, 1) : ℤ × ℤ) = p := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := slice_disjoint (K := K) hϖ (mk_localRepInf_mem_slice (K := K) ϖ hϖ0) h
      exact Prod.ext h1 h2
    · rintro rfl
      exact mk_localRepInf_mem_slice (K := K) ϖ hϖ0

  rw [ct_eq_sum (R := R) ϖ T p hsupp, hTF, Finset.sum_union hdisj, Finset.sum_singleton,
    Finset.sum_image fun r _ r' _ h => hψinj h]
  congr 1
  · calc ∑ r : R ⧸ Ideal.span {ϖ}, Set.indicator (slice (R := R) (K := K) ϖ p.1 p.2)
          (fun c => (T : GL (Fin 2) K → R₀) (Quotient.out c)) (ψ r)
        = ∑ _r : R ⧸ Ideal.span {ϖ}, (if ((1, 0) : ℤ × ℤ) = p then (1 : R₀) else 0) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Set.indicator_apply, hvalψ]
          exact if_congr (hmemψ r) rfl rfl
      _ = if ((1, 0) : ℤ × ℤ) = p then (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) else 0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
          split_ifs <;> simp
  · rw [Set.indicator_apply, hvalInf]
    exact if_congr hmemInf rfl rfl

private theorem ct_heckeIndicator_central [IsFractionRing R K] (hϖ : Irreducible ϖ)
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    (p : ℤ × ℤ) :
    ct (R := R) (K := K) ϖ ((heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS :
        HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
      if ((1, 1) : ℤ × ℤ) = p then (1 : R₀) else 0 := by
  classical
  set ζ : GL (Fin 2) K := diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 with hζ
  set Y : HeckeAlgebra (integralSubgroup R K) R₀ := heckeIndicator R₀ ζ hS
  set cζ : GL (Fin 2) K ⧸ integralSubgroup R K := QuotientGroup.mk ζ with hcζ
  have hsupp : QuotientGroup.mk '' Function.support (Y : GL (Fin 2) K → R₀) ⊆
      ((({cζ} : Finset (GL (Fin 2) K ⧸ integralSubgroup R K)) : Set (GL (Fin 2) K ⧸ integralSubgroup R K))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxD : x ∈ doubleCoset (integralSubgroup R K) ζ := by
      by_contra hxD
      exact hx (heckeIndicator_apply_of_notMem _ hxD)
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hxD
    rw [Finset.coe_singleton, Set.mem_singleton_iff, hcζ, QuotientGroup.eq, hζ,
      mul_diagPi_mul_localRepInf_comm (K := K) ϖ hϖ0 u]
    have hw : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * u * v)⁻¹ * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) =
        v⁻¹ * u⁻¹ := by
      group
    rw [hw]
    exact mul_mem (inv_mem hv) (inv_mem hu)
  have hval : (Y : GL (Fin 2) K → R₀) (Quotient.out cζ) = 1 := by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (integralSubgroup R K) ζ
    rw [hcζ, hv]
    exact heckeIndicator_apply_of_mem _ (mem_doubleCoset_iff.mpr ⟨1, one_mem _, v, v.2, by rw [one_mul]⟩)
  have hmem : cζ ∈ slice (R := R) (K := K) ϖ p.1 p.2 ↔ ((1, 1) : ℤ × ℤ) = p := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ :=
        slice_disjoint (K := K) hϖ (mk_diagPi_mul_localRepInf_mem_slice (K := K) ϖ hϖ0) h
      exact Prod.ext h1 h2
    · rintro rfl
      exact mk_diagPi_mul_localRepInf_mem_slice (K := K) ϖ hϖ0
  rw [ct_eq_sum (R := R) ϖ Y p hsupp, Finset.sum_singleton, Set.indicator_apply, hval]
  exact if_congr hmem rfl rfl

private theorem ctAlgHom_heckeIndicator_diagPi [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] :
    ctAlgHom (K := K) (R₀ := R₀) hϖ (heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) =
      AddMonoidAlgebra.single (1, 0) (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) + AddMonoidAlgebra.single (0, 1) 1 := by
  classical
  refine AddMonoidAlgebra.ext <| Finsupp.ext fun p => ?_
  change ct (R := R) (K := K) ϖ ((heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ) :
      HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p =
    Finsupp.single ((1, 0) : ℤ × ℤ) (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) p +
      Finsupp.single ((0, 1) : ℤ × ℤ) (1 : R₀) p
  rw [ct_heckeIndicator_diagPi (K := K) ϖ hϖ0 hϖ p, Finsupp.single_apply, Finsupp.single_apply]

private theorem ctAlgHom_heckeIndicator_central [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (hϖ : Irreducible ϖ)
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ctAlgHom (K := K) (R₀ := R₀) hϖ (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) =
      AddMonoidAlgebra.single (1, 1) 1 := by
  classical
  refine AddMonoidAlgebra.ext <| Finsupp.ext fun p => ?_
  change ct (R := R) (K := K) ϖ ((heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS :
      HeckeAlgebra (integralSubgroup R K) R₀) : GL (Fin 2) K → R₀) p = Finsupp.single ((1, 1) : ℤ × ℤ) (1 : R₀) p
  rw [ct_heckeIndicator_central (K := K) ϖ hϖ0 hϖ hS p, Finsupp.single_apply]

end Generators

end LocalGL2.IwasawaSlice

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ S : HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ),
      (∀ (f : HeckeAlgebra (integralSubgroup R K) R₀) (a b : ℤ),
        (S f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) K ⧸ integralSubgroup R K,
          Set.indicator
            {c : GL (Fin 2) K ⧸ integralSubgroup R K | ∃ g : GL (Fin 2) K, QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b}
            (fun c => (f : GL (Fin 2) K → R₀) (Quotient.out c)) c) ∧
      S (heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) =
        AddMonoidAlgebra.single (1, 0) (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) +
          AddMonoidAlgebra.single (0, 1) 1 ∧
      S (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) = AddMonoidAlgebra.single (1, 1) 1 := by
  exact ⟨LocalGL2.IwasawaSlice.ctAlgHom (K := K) (R₀ := R₀) hϖ, fun f a b => rfl,
    LocalGL2.IwasawaSlice.ctAlgHom_heckeIndicator_diagPi (K := K) ϖ hϖ0 hϖ,
    LocalGL2.IwasawaSlice.ctAlgHom_heckeIndicator_central (K := K) ϖ hϖ0 hϖ hS⟩

#print axioms solution

end S_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq
end P2MW
export P2MW.S_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq (solution)
