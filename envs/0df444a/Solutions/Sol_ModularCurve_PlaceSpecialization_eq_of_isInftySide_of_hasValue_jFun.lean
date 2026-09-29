-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.eq_of_isInftySide_of_hasValue_jFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8077be61-ba49-5e6f-8126-a10ee47558f3

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_Polynomial_roots_filter_valuation_eq_singleton_of_kroneckerShape
import Theorems.Thm_ModularCurve_existsUnique_kroneckerRemainder
import Theorems.Thm_ModularCurve_natDegree_kroneckerRemainder_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open AlgebraicCurve IsLocalRing ModularCurve Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace CuspUniq

open MvPolynomial in

theorem mem_span_X_sub_C_of_eval_eq_zero {R σ : Type*} [CommRing R] (a : σ → R)
    (p : MvPolynomial σ R) (hp : MvPolynomial.eval a p = 0) :
    p ∈ Ideal.span (Set.range fun i : σ => (MvPolynomial.X i - MvPolynomial.C (a i) : MvPolynomial σ R)) := by
  set I := Ideal.span (Set.range fun i : σ => (MvPolynomial.X i - MvPolynomial.C (a i) : MvPolynomial σ R)) with hI
  have key : (Ideal.Quotient.mk I).comp (RingHom.id _) =
      (Ideal.Quotient.mk I).comp (MvPolynomial.C.comp (MvPolynomial.eval a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i
      simp only [RingHom.comp_apply, RingHom.id_apply, MvPolynomial.eval_X]
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨i, rfl⟩
  have := congrArg (fun f => f p) key
  simp only [RingHom.comp_apply, RingHom.id_apply, hp, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

open MvPolynomial in
theorem exists_eq_sum_mul_X_sub_C {R σ : Type*} [CommRing R] [Fintype σ] (a : σ → R)
    (p : MvPolynomial σ R) (hp : MvPolynomial.eval a p = 0) :
    ∃ c : σ → MvPolynomial σ R, p = ∑ i, c i * (MvPolynomial.X i - MvPolynomial.C (a i)) := by
  have h := mem_span_X_sub_C_of_eval_eq_zero a p hp
  rw [Ideal.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

section HasValue

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem HasValue.add' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem HasValue.neg' {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem HasValue.sub' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact HasValue.add' h (HasValue.neg' h')

theorem HasValue.pow' {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using v.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem hasValue_aeval {σ : Type*} (g : σ → F) (a : σ → K) (h : ∀ i, v.HasValue (g i) (a i))
    (p : MvPolynomial σ K) : v.HasValue (MvPolynomial.aeval g p) (MvPolynomial.eval a p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using v.hasValue_algebraMap c
  | add p q hp hq => rw [map_add, map_add]; exact HasValue.add' hp hq
  | mul_X p i hp => rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]; exact hp.mul (h i)

theorem HasValue.eval₂_int' {g : F} {a : K} (h : v.HasValue g a) (c : Polynomial ℤ) :
    v.HasValue (c.eval₂ (Int.castRingHom F) g) (c.eval₂ (Int.castRingHom K) a) := by
  induction c using Polynomial.induction_on' with
  | add p r hp hr => rw [eval₂_add, eval₂_add]; exact HasValue.add' hp hr
  | monomial n z =>
    rw [eval₂_monomial, eval₂_monomial]
    have hz : v.HasValue ((z : ℤ) : F) ((z : ℤ) : K) := by simpa using v.hasValue_algebraMap (z : K)
    simpa using hz.mul (HasValue.pow' h n)

theorem HasValue.eval₂_bivariate' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a')
    (Φ : Polynomial (Polynomial ℤ)) :
    v.HasValue (Φ.eval₂ (eval₂RingHom (Int.castRingHom F) g) g') (Φ.eval₂ (eval₂RingHom (Int.castRingHom K) a) a') := by
  induction Φ using Polynomial.induction_on' with
  | add p r hp hr => rw [eval₂_add, eval₂_add]; exact HasValue.add' hp hr
  | monomial n c =>
    rw [eval₂_monomial, eval₂_monomial]
    exact (HasValue.eval₂_int' h c).mul (HasValue.pow' h' n)

theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  have h0 := v.ord_nonneg_of_mem h.mem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    have := (residue_ne_zero_iff_isUnit _).mpr hu
    exact this (by rw [h.residue_eq, map_zero])

end HasValue

end CuspUniq

namespace CuspUniq

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

p2m_open "ModularCurve.PlaceSpecialization"

theorem coe_jFun : ((jFun (q := q) : FF) : LaurentSeries ℚbar) = coeffEmb ℚbar jq := rfl
theorem coe_jqFun : ((jqFun (q := q) : FF) : LaurentSeries ℚbar) = coeffEmb ℚbar (qExpand ℚ (1 * q) jq) := rfl

theorem coe_algebraMap_FF (c : ℚbar) :
    ((algebraMap ℚbar FF c : FF) : LaurentSeries ℚbar) = HahnSeries.single (0 : ℤ) c := by
  show algebraMap ℚbar (LaurentSeries ℚbar) c = HahnSeries.single (0 : ℤ) c
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

theorem jFun_ne_algebraMap (c : ℚbar) : (jFun (q := q) : FF) ≠ algebraMap ℚbar FF c := by
  intro h
  have h1 := congrArg (fun f : FF => (f : LaurentSeries ℚbar).coeff (-1)) h
  simp only [coe_jFun, coeffEmb_coeff, coeff_jq_neg_one, map_one, coe_algebraMap_FF] at h1
  rw [HahnSeries.coeff_single_of_ne (by norm_num)] at h1
  exact one_ne_zero h1

theorem jFun_ne_zero' : (jFun (q := q) : FF) ≠ 0 := by
  have := jFun_ne_algebraMap (q := q) 0
  rwa [map_zero] at this

theorem jqFun_ne_zero' : (jqFun (q := q) : FF) ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : FF => (f : LaurentSeries ℚbar).coeff (-(((1 * q : ℕ) : ℤ)))) h
  simp only [coe_jqFun, coeffEmb_coeff, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
  rw [show (-(((1 * q : ℕ) : ℤ))) = ((1 * q : ℕ) : ℤ) * (-1) by ring, qExpand_coeff_mul, coeff_jq_neg_one,
    map_one] at h1
  exact one_ne_zero h1

theorem jqFun_eq_tInfty_mul : (jqFun (q := q) : FF) = tInfty (q := q) * jFun (q := q) ^ (1 * q) := by
  rw [tInfty, div_mul_cancel₀ _ (pow_ne_zero _ jFun_ne_zero')]

theorem modeq_jFun_jqFun' :
    data.Φ.eval₂ (eval₂RingHom (Int.castRingHom FF) (jFun (q := q))) (jqFun (q := q)) = 0 := by
  apply Subtype.val_injective
  set ι : FF →+* LaurentSeries ℚbar := (algebraMap FF (LaurentSeries ℚbar)) with hι
  have hιapp : ∀ z : FF, ι z = (z : LaurentSeries ℚbar) := fun z => rfl
  show ((data.Φ.eval₂ (eval₂RingHom (Int.castRingHom FF) (jFun (q := q))) (jqFun (q := q)) : FF) : LaurentSeries ℚbar)
    = ((0 : FF) : LaurentSeries ℚbar)
  rw [← hιapp, ← hιapp, map_zero, Polynomial.hom_eval₂]
  have h0 := congrArg (coeffEmb ℚbar) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h0
  have hhom : ι.comp (eval₂RingHom (Int.castRingHom FF) (jFun (q := q))) = (coeffEmb ℚbar).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, evalAtJ_X, hιapp]; rfl
  have harg : ι (jqFun (q := q)) = coeffEmb ℚbar (jqN q) := by
    rw [hιapp, coe_jqFun, jqN, qExpand_congr (one_mul q)]
  rw [hhom, harg]
  exact h0

theorem valuation_eval₂_le_pow' {K : Type*} [Field K] (B : ValuationSubring K) {x : K} (hx : 1 ≤ B.valuation x)
    (c : Polynomial ℤ) {d : ℕ} (hc : c.natDegree ≤ d) :
    B.valuation (c.eval₂ (Int.castRingHom K) x) ≤ B.valuation x ^ d := by
  rw [eval₂_eq_sum_range' (Int.castRingHom K) (show c.natDegree < d + 1 by omega) x]
  apply Valuation.map_sum_le
  intro i hi
  rw [Finset.mem_range] at hi
  rw [map_mul, map_pow]
  have hz : B.valuation ((Int.castRingHom K) (c.coeff i)) ≤ 1 := by
    have h := B.valuation_le_one ((c.coeff i : ℤ) : B)
    rw [show (((c.coeff i : ℤ) : B) : K) = (Int.castRingHom K) (c.coeff i) from by push_cast; rfl] at h
    exact h
  calc B.valuation ((Int.castRingHom K) (c.coeff i)) * B.valuation x ^ i ≤ 1 * B.valuation x ^ i :=
        mul_le_mul_left hz _
    _ = B.valuation x ^ i := one_mul _
    _ ≤ B.valuation x ^ d := pow_le_pow_right₀ hx (by omega)

def PsiAt (data : ModularPolynomialData q) (x₀ : ℚbar) : Polynomial ℚbar :=
  data.Φ.map (eval₂RingHom (Int.castRingHom ℚbar) x₀)

theorem psiAt_shape (hKr : KroneckerCongruence q data) (x₀ : ℚbar) (hvx : 1 < A.valuation x₀) :
    ∃ H : Polynomial ℚbar,
      PsiAt data x₀ = (C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C ((q : ℕ) : ℚbar) * H ∧
      H.natDegree ≤ q ∧ (∀ b < q, A.valuation (H.coeff b) ≤ A.valuation x₀ ^ q) ∧
      A.valuation (H.coeff q) ≤ A.valuation x₀ ^ (q - 1) := by
  set v := A.valuation with hv
  obtain ⟨R, hR, -⟩ := existsUnique_kroneckerRemainder q data hKr
  obtain ⟨hRdeg, hRX, hRqq⟩ := natDegree_kroneckerRemainder_le q data R hR
  set H : Polynomial ℚbar := R.map (eval₂RingHom (Int.castRingHom ℚbar) x₀) with hH
  refine ⟨H, ?_, (natDegree_map_le).trans hRdeg, ?_, ?_⟩
  · rw [PsiAt, hR]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      coe_eval₂RingHom, eval₂_X, eval₂_C, eq_intCast, Int.cast_natCast, hH]
    simp
  · intro b _
    rw [hH, coeff_map, coe_eval₂RingHom]
    exact valuation_eval₂_le_pow' A hvx.le _ (hRX b)
  · rw [hH, coeff_map, coe_eval₂RingHom]
    apply valuation_eval₂_le_pow' A hvx.le
    have h1 := hRX q
    rcases h1.lt_or_eq with hlt | heq
    · omega
    · have : (R.coeff q).leadingCoeff = 0 := by rw [leadingCoeff, heq, hRqq]
      rw [leadingCoeff_eq_zero] at this
      rw [this, natDegree_zero]; omega

theorem valuation_natCast_q_le : A.valuation ((q : ℕ) : ℚbar) ≤ 1 := by
  have h := A.valuation_le_one ((q : ℕ) : A)
  rwa [show (((q : ℕ) : A) : ℚbar) = ((q : ℕ) : ℚbar) from by push_cast; rfl] at h

theorem exists_bigRoot (hKr : KroneckerCongruence q data) (x₀ : ℚbar) (hvx : 1 < A.valuation x₀) :
    ∃ y₀ : ℚbar, ((PsiAt data x₀).roots.filter fun y => A.valuation y = A.valuation x₀ ^ q) = {y₀} := by
  classical
  obtain ⟨H, hΨ, hHdeg, hHb, hHq⟩ := psiAt_shape (A := A) hKr x₀ hvx
  rw [hΨ]
  exact Polynomial.roots_filter_valuation_eq_singleton_of_kroneckerShape A.valuation
    (Fact.out : q.Prime).one_lt x₀ _ hvx valuation_natCast_q_le H hHdeg hHb hHq (IsAlgClosed.splits _)

open Classical in

def bigRoot (A : ValuationSubring (AlgebraicClosure ℚ)) (hKr : KroneckerCongruence q data) (x₀ : ℚbar) : ℚbar :=
  if h : 1 < A.valuation x₀ then (exists_bigRoot (A := A) hKr x₀ h).choose else 0

open Classical in
theorem bigRoot_spec (hKr : KroneckerCongruence q data) {x₀ : ℚbar} (hvx : 1 < A.valuation x₀) :
    ((PsiAt data x₀).roots.filter fun y => A.valuation y = A.valuation x₀ ^ q) = {bigRoot A hKr x₀} := by
  rw [bigRoot, dif_pos hvx]
  exact (exists_bigRoot (A := A) hKr x₀ hvx).choose_spec

theorem psiAt_ne_zero (hKr : KroneckerCongruence q data) (x₀ : ℚbar) (hvx : 1 < A.valuation x₀) :
    PsiAt data x₀ ≠ 0 := by
  classical
  intro h0
  have := bigRoot_spec (A := A) hKr hvx
  rw [h0, roots_zero, Multiset.filter_zero] at this
  exact (Multiset.singleton_ne_zero _ this.symm)

theorem eq_bigRoot_of_isRoot (hKr : KroneckerCongruence q data) {x₀ y : ℚbar} (hvx : 1 < A.valuation x₀)
    (hy : (PsiAt data x₀).IsRoot y) (hvy : A.valuation y = A.valuation x₀ ^ q) : y = bigRoot A hKr x₀ := by
  classical
  have hmem : y ∈ ((PsiAt data x₀).roots.filter fun y => A.valuation y = A.valuation x₀ ^ q) := by
    rw [Multiset.mem_filter, mem_roots (psiAt_ne_zero (A := A) hKr x₀ hvx)]
    exact ⟨hy, hvy⟩
  rw [bigRoot_spec (A := A) hKr hvx] at hmem
  exact Multiset.mem_singleton.mp hmem

theorem rootMultiplicity_bigRoot (hKr : KroneckerCongruence q data) {x₀ : ℚbar} (hvx : 1 < A.valuation x₀) :
    (PsiAt data x₀).rootMultiplicity (bigRoot A hKr x₀) = 1 := by
  classical
  set y₀ := bigRoot A hKr x₀
  have hspec := bigRoot_spec (A := A) hKr hvx
  have hmem : y₀ ∈ ((PsiAt data x₀).roots.filter fun y => A.valuation y = A.valuation x₀ ^ q) := by
    rw [hspec]; exact Multiset.mem_singleton_self _
  have hbig : A.valuation y₀ = A.valuation x₀ ^ q := (Multiset.mem_filter.mp hmem).2
  rw [← count_roots]
  have : Multiset.count y₀ ((PsiAt data x₀).roots.filter fun y => A.valuation y = A.valuation x₀ ^ q)
      = Multiset.count y₀ (PsiAt data x₀).roots := Multiset.count_filter_of_pos hbig
  rw [← this, hspec, Multiset.count_singleton_self]

theorem bigRoot_ne_zero (hKr : KroneckerCongruence q data) {x₀ : ℚbar} (hvx : 1 < A.valuation x₀) :
    bigRoot A hKr x₀ ≠ 0 := by
  classical
  have hspec := bigRoot_spec (A := A) hKr hvx
  have hmem : bigRoot A hKr x₀ ∈ ((PsiAt data x₀).roots.filter fun y => A.valuation y = A.valuation x₀ ^ q) := by
    rw [hspec]; exact Multiset.mem_singleton_self _
  have hbig : A.valuation (bigRoot A hKr x₀) = A.valuation x₀ ^ q := (Multiset.mem_filter.mp hmem).2
  intro h0
  rw [h0, map_zero] at hbig
  exact (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hvx))) hbig.symm

end CuspUniq

namespace CuspUniq

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

p2m_open "ModularCurve.PlaceSpecialization"

def gen (q : ℕ) [Fact q.Prime] : Fin 4 → ↥(modularFunctionFieldBar (1 * q)) := fun i =>
  match i with
  | 0 => jFun (q := q)
  | 1 => jqFun (q := q)
  | 2 => (jFun (q := q))⁻¹
  | 3 => (jqFun (q := q))⁻¹

@[scoped simp] theorem gen_zero : gen q 0 = jFun (q := q) := rfl
@[scoped simp] theorem gen_one : gen q 1 = jqFun (q := q) := rfl
@[scoped simp] theorem gen_two : gen q 2 = (jFun (q := q))⁻¹ := rfl
@[scoped simp] theorem gen_three : gen q 3 = (jqFun (q := q))⁻¹ := rfl

omit [Fact q.Prime] in

def pt (x₀ y₀ : ℚbar) : Fin 4 → ℚbar := fun i =>
  match i with
  | 0 => x₀
  | 1 => y₀
  | 2 => x₀⁻¹
  | 3 => y₀⁻¹

omit [Fact q.Prime] in
@[scoped simp] theorem pt_zero (x₀ y₀ : ℚbar) : pt x₀ y₀ 0 = x₀ := rfl
omit [Fact q.Prime] in
@[scoped simp] theorem pt_one (x₀ y₀ : ℚbar) : pt x₀ y₀ 1 = y₀ := rfl
omit [Fact q.Prime] in
@[scoped simp] theorem pt_two (x₀ y₀ : ℚbar) : pt x₀ y₀ 2 = x₀⁻¹ := rfl
omit [Fact q.Prime] in
@[scoped simp] theorem pt_three (x₀ y₀ : ℚbar) : pt x₀ y₀ 3 = y₀⁻¹ := rfl

theorem hasValue_gen {W : Place ℚbar FF} {x₀ y₀ : ℚbar} (hx : W.HasValue (jFun (q := q)) x₀)
    (hy : W.HasValue (jqFun (q := q)) y₀) (hx0 : x₀ ≠ 0) (hy0 : y₀ ≠ 0) :
    ∀ i, W.HasValue (gen q i) (pt x₀ y₀ i) := by
  intro i
  match i with
  | 0 => exact hx
  | 1 => exact hy
  | 2 => exact hx.inv hx0
  | 3 => exact hy.inv hy0

theorem inftySide_facts (P : PlaceSpecialization A q 1 data hKr k red hα hβ) {W : Place ℚbar FF}
    (hW : P.IsInftySide W) {x₀ : ℚbar} (hx : W.HasValue (jFun (q := q)) x₀) :
    1 < A.valuation x₀ ∧ x₀ ≠ 0 ∧ W.HasValue (jqFun (q := q)) (bigRoot A hKr x₀) := by
  obtain ⟨hcusp, τ, hτ, hτval⟩ := hW
  set v := A.valuation with hv

  have hx₀A : ∀ a : A, (a : ℚbar) ≠ x₀ := by
    intro a ha
    have hval : W.HasValue (jFun (q := q) - algebraMap ℚbar FF (a : ℚbar)) 0 := by
      have := HasValue.sub' hx (W.hasValue_algebraMap (a : ℚbar))
      rwa [← ha, sub_self] at this
    have hne : jFun (q := q) - algebraMap ℚbar FF (a : ℚbar) ≠ 0 :=
      sub_ne_zero.mpr (jFun_ne_algebraMap _)
    have hpos := ord_pos_of_hasValue_zero hval hne
    exact absurd (hcusp a) (not_le.mpr hpos)
  have hvx : 1 < v x₀ := by
    rw [← not_le, hv, A.valuation_le_one_iff]
    intro hmem
    exact hx₀A ⟨x₀, hmem⟩ rfl
  have hx0 : x₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvx; exact not_lt_zero' hvx

  have hτ1 : v (τ : ℚbar) = 1 := by
    have hker : τ - 1 ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_sub, map_one, hτ, sub_self]
    have hmax : τ - 1 ∈ maximalIdeal A := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) hker
    have hlt : v ((τ : ℚbar) - 1) < 1 := by
      have := (A.valuation_lt_one_iff (τ - 1)).mp hmax
      push_cast at this
      exact this
    have : (τ : ℚbar) = 1 + ((τ : ℚbar) - 1) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left]
    · exact map_one v
    · rwa [map_one]

  have hy : W.HasValue (jqFun (q := q)) ((τ : ℚbar) * x₀ ^ (1 * q)) := by
    rw [jqFun_eq_tInfty_mul]
    exact hτval.mul (HasValue.pow' hx _)
  have hvy : v ((τ : ℚbar) * x₀ ^ (1 * q)) = v x₀ ^ q := by
    rw [map_mul, hτ1, one_mul, map_pow, Nat.one_mul]

  have hroot : (PsiAt data x₀).IsRoot ((τ : ℚbar) * x₀ ^ (1 * q)) := by
    rw [IsRoot.def, PsiAt, eval_map]
    have h1 := HasValue.eval₂_bivariate' hx hy data.Φ
    rw [modeq_jFun_jqFun'] at h1
    have h0 : W.HasValue (0 : FF) (0 : ℚbar) := by simpa using W.hasValue_algebraMap (0 : ℚbar)
    exact (h1.unique h0)
  refine ⟨hvx, hx0, ?_⟩
  rwa [← eq_bigRoot_of_isRoot (A := A) hKr hvx hroot hvy]

theorem exists_diff_inner (x₀ : ℚbar) (a : Polynomial ℤ) :
    ∃ pe : MvPolynomial (Fin 4) ℚbar,
      algebraMap ℚbar FF (a.eval₂ (Int.castRingHom ℚbar) x₀) - a.eval₂ (Int.castRingHom FF) (jFun (q := q)) =
        (algebraMap ℚbar FF x₀ - jFun (q := q)) * MvPolynomial.aeval (gen q) pe := by
  induction a using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨pe₁, h₁⟩ := hp
    obtain ⟨pe₂, h₂⟩ := hr
    refine ⟨pe₁ + pe₂, ?_⟩
    simp only [eval₂_add, map_add]
    linear_combination h₁ + h₂
  | monomial n z =>
    refine ⟨MvPolynomial.C (z : ℚbar) *
      ∑ i ∈ Finset.range n, MvPolynomial.C (x₀ ^ i) * MvPolynomial.X 0 ^ (n - 1 - i), ?_⟩
    rw [eval₂_monomial, eval₂_monomial, map_mul, map_pow]
    simp only [map_mul, map_sum, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, gen_zero,
      eq_intCast, map_intCast]
    have hg := geom_sum₂_mul (algebraMap ℚbar FF x₀) (jFun (q := q)) n
    linear_combination (-(z : FF)) * hg

theorem exists_diff (x₀ : ℚbar) (Φ' : Polynomial (Polynomial ℤ)) :
    ∃ pd : MvPolynomial (Fin 4) ℚbar,
      Φ'.eval₂ ((algebraMap ℚbar FF).comp (eval₂RingHom (Int.castRingHom ℚbar) x₀)) (jqFun (q := q)) -
        Φ'.eval₂ (eval₂RingHom (Int.castRingHom FF) (jFun (q := q))) (jqFun (q := q)) =
        (algebraMap ℚbar FF x₀ - jFun (q := q)) * MvPolynomial.aeval (gen q) pd := by
  induction Φ' using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨pd₁, h₁⟩ := hp
    obtain ⟨pd₂, h₂⟩ := hr
    refine ⟨pd₁ + pd₂, ?_⟩
    simp only [eval₂_add, map_add]
    linear_combination h₁ + h₂
  | monomial n a =>
    obtain ⟨pe, he⟩ := exists_diff_inner (q := q) x₀ a
    refine ⟨pe * MvPolynomial.X 1 ^ n, ?_⟩
    rw [eval₂_monomial, eval₂_monomial, RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, map_mul, map_pow,
      MvPolynomial.aeval_X, gen_one]
    linear_combination (jqFun (q := q)) ^ n * he

def PsiOne (A : ValuationSubring (AlgebraicClosure ℚ)) (hKr : KroneckerCongruence q data) (x₀ : ℚbar) : Polynomial ℚbar :=
  PsiAt data x₀ /ₘ (X - C (bigRoot A hKr x₀))

theorem psiAt_eq_mul (hKr : KroneckerCongruence q data) {x₀ : ℚbar} (hvx : 1 < A.valuation x₀) :
    (X - C (bigRoot A hKr x₀)) * PsiOne A hKr x₀ = PsiAt data x₀ := by
  classical
  rw [PsiOne, mul_divByMonic_eq_iff_isRoot, ← mem_roots (psiAt_ne_zero (A := A) hKr x₀ hvx)]
  have hspec := bigRoot_spec (A := A) hKr hvx
  have hmem : bigRoot A hKr x₀ ∈ ((PsiAt data x₀).roots.filter fun y => A.valuation y = A.valuation x₀ ^ q) := by
    rw [hspec]; exact Multiset.mem_singleton_self _
  exact (Multiset.mem_filter.mp hmem).1

theorem eval_psiOne_ne_zero (hKr : KroneckerCongruence q data) {x₀ : ℚbar} (hvx : 1 < A.valuation x₀) :
    (PsiOne A hKr x₀).eval (bigRoot A hKr x₀) ≠ 0 := by
  have h := eval_divByMonic_pow_rootMultiplicity_ne_zero (bigRoot A hKr x₀) (psiAt_ne_zero (A := A) hKr x₀ hvx)
  rwa [rootMultiplicity_bigRoot (A := A) hKr hvx, pow_one] at h

def pk (A : ValuationSubring (AlgebraicClosure ℚ)) (hKr : KroneckerCongruence q data) (x₀ : ℚbar) : MvPolynomial (Fin 4) ℚbar :=
  (PsiOne A hKr x₀).eval₂ (MvPolynomial.C) (MvPolynomial.X 1)

theorem aeval_pk (hKr : KroneckerCongruence q data) (x₀ : ℚbar) :
    MvPolynomial.aeval (gen q) (pk A hKr x₀) = Polynomial.aeval (jqFun (q := q)) (PsiOne A hKr x₀) := by
  rw [pk, show (MvPolynomial.aeval (gen q)) ((PsiOne A hKr x₀).eval₂ MvPolynomial.C (MvPolynomial.X 1))
      = (MvPolynomial.aeval (gen q)).toRingHom ((PsiOne A hKr x₀).eval₂ MvPolynomial.C (MvPolynomial.X 1)) from rfl,
    Polynomial.hom_eval₂, Polynomial.aeval_def]
  congr 1
  · ext c; simp
  · simp

theorem eval_pk (hKr : KroneckerCongruence q data) (x₀ y₀ : ℚbar) :
    MvPolynomial.eval (pt x₀ y₀) (pk A hKr x₀) = (PsiOne A hKr x₀).eval y₀ := by
  rw [pk, Polynomial.hom_eval₂, Polynomial.eval]
  congr 1
  · ext c; simp
  · simp

theorem key_relation (hKr : KroneckerCongruence q data) {x₀ : ℚbar} (hvx : 1 < A.valuation x₀) :
    ∃ pd : MvPolynomial (Fin 4) ℚbar,
      (jqFun (q := q) - algebraMap ℚbar FF (bigRoot A hKr x₀)) * MvPolynomial.aeval (gen q) (pk A hKr x₀) =
        (algebraMap ℚbar FF x₀ - jFun (q := q)) * MvPolynomial.aeval (gen q) pd := by
  obtain ⟨pd, hd⟩ := exists_diff (q := q) x₀ data.Φ
  refine ⟨pd, ?_⟩
  rw [modeq_jFun_jqFun', sub_zero, ← Polynomial.eval₂_map, ← PsiAt.eq_def] at hd

  rw [← hd, aeval_pk, Polynomial.aeval_def, ← psiAt_eq_mul (A := A) hKr hvx, eval₂_mul, eval₂_sub, eval₂_X,
    eval₂_C]

end CuspUniq
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun.CuspUniq"

namespace CuspUniq

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

p2m_open "ModularCurve.PlaceSpecialization"

omit [Fact q.Prime] in
theorem ord_jFun_sub_pos' {q : ℕ} [Fact q.Prime] {W : Place ℚbar ↥(modularFunctionFieldBar (1 * q))} {x₀ : ℚbar}
    (hx : W.HasValue (jFun (q := q)) x₀) : 0 < W.ord (jFun (q := q) - algebraMap ℚbar _ x₀) := by
  have hval : W.HasValue (jFun (q := q) - algebraMap ℚbar _ x₀) 0 := by
    simpa using HasValue.sub' hx (W.hasValue_algebraMap x₀)
  exact ord_pos_of_hasValue_zero hval (sub_ne_zero.mpr (jFun_ne_algebraMap _))

section Induction

variable (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
  {W W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} {x₀ : AlgebraicClosure ℚ}
  (hW : P.IsInftySide W) (hW' : P.IsInftySide W')
  (hx : W.HasValue (jFun (q := q)) x₀) (hx' : W'.HasValue (jFun (q := q)) x₀)
include hW hW' hx hx'

theorem ord_aeval_proportional (p : MvPolynomial (Fin 4) ℚbar) (hp : MvPolynomial.aeval (gen q) p ≠ 0) :
    W'.ord (jFun (q := q) - algebraMap ℚbar FF x₀) * W.ord (MvPolynomial.aeval (gen q) p) =
      W.ord (jFun (q := q) - algebraMap ℚbar FF x₀) * W'.ord (MvPolynomial.aeval (gen q) p) := by
  classical
  obtain ⟨hvx, hx0, hy⟩ := inftySide_facts P hW hx
  obtain ⟨-, -, hy'⟩ := inftySide_facts P hW' hx'
  set y₀ := bigRoot A hKr x₀ with hy₀
  have hy0 : y₀ ≠ 0 := bigRoot_ne_zero (A := A) hKr hvx
  set e := W.ord (jFun (q := q) - algebraMap ℚbar FF x₀) with he
  set e' := W'.ord (jFun (q := q) - algebraMap ℚbar FF x₀) with he'
  have he0 : 0 < e := ord_jFun_sub_pos' hx
  have he0' : 0 < e' := ord_jFun_sub_pos' hx'
  have hgen : ∀ i, W.HasValue (gen q i) (pt x₀ y₀ i) := hasValue_gen hx hy hx0 hy0
  have hgen' : ∀ i, W'.HasValue (gen q i) (pt x₀ y₀ i) := hasValue_gen hx' hy' hx0 hy0
  have hjx : jFun (q := q) - algebraMap ℚbar FF x₀ ≠ 0 := sub_ne_zero.mpr (jFun_ne_algebraMap _)

  obtain ⟨pd, hrel⟩ := key_relation (q := q) (A := A) hKr hvx
  set kk := MvPolynomial.aeval (gen q) (pk A hKr x₀) with hkk
  set dd := MvPolynomial.aeval (gen q) pd with hdd
  have hkval : W.HasValue kk ((PsiOne A hKr x₀).eval y₀) := by
    rw [hkk, ← eval_pk (A := A) hKr x₀ y₀]; exact hasValue_aeval _ _ hgen _
  have hkval' : W'.HasValue kk ((PsiOne A hKr x₀).eval y₀) := by
    rw [hkk, ← eval_pk (A := A) hKr x₀ y₀]; exact hasValue_aeval _ _ hgen' _
  have hkne : (PsiOne A hKr x₀).eval y₀ ≠ 0 := eval_psiOne_ne_zero (A := A) hKr hvx
  have hk0 : kk ≠ 0 := hkval.ne_zero hkne
  have hordk : W.ord kk = 0 := hkval.ord_eq_zero hkne
  have hordk' : W'.ord kk = 0 := hkval'.ord_eq_zero hkne

  set J : FF := jFun (q := q) with hJ
  set Jq : FF := jqFun (q := q) with hJq
  set X0 : FF := algebraMap ℚbar FF x₀ with hX0
  set Y0 : FF := algebraMap ℚbar FF y₀ with hY0
  have hJ0 : J ≠ 0 := jFun_ne_zero'
  have hJq0 : Jq ≠ 0 := jqFun_ne_zero'
  have hX00 : X0 ≠ 0 := (_root_.map_ne_zero _).mpr hx0
  have hY00 : Y0 ≠ 0 := (_root_.map_ne_zero _).mpr hy0
  have hrel' : (Jq - Y0) * kk = (X0 - J) * dd := hrel
  have h0 : kk * (J - X0) = (J - X0) * kk := by ring
  have h1 : kk * (Jq - Y0) = (J - X0) * (-dd) := by linear_combination hrel'
  have h2 : kk * (J⁻¹ - X0⁻¹) = (J - X0) * (-(kk * J⁻¹ * X0⁻¹)) := by
    field_simp
    ring
  have h3 : kk * (Jq⁻¹ - Y0⁻¹) = (J - X0) * (dd * Jq⁻¹ * Y0⁻¹) := by
    have : kk * (Jq⁻¹ - Y0⁻¹) = -((Jq - Y0) * kk) * Jq⁻¹ * Y0⁻¹ := by
      field_simp
      ring
    rw [this, hrel']
    ring

  suffices H : ∀ n : ℕ, ∀ p : MvPolynomial (Fin 4) ℚbar, MvPolynomial.aeval (gen q) p ≠ 0 →
      (W'.ord (MvPolynomial.aeval (gen q) p)).toNat = n →
      e' * W.ord (MvPolynomial.aeval (gen q) p) = e * W'.ord (MvPolynomial.aeval (gen q) p) from
    H _ p hp rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro p hp hn
  by_cases hpt : MvPolynomial.eval (pt x₀ y₀) p = 0
  ·
    obtain ⟨c, hc⟩ := exists_eq_sum_mul_X_sub_C (pt x₀ y₀) p hpt
    set p' : MvPolynomial (Fin 4) ℚbar :=
      c 0 * pk A hKr x₀ - c 1 * pd - c 2 * (pk A hKr x₀ * MvPolynomial.X 2 * MvPolynomial.C x₀⁻¹)
        + c 3 * (pd * MvPolynomial.X 3 * MvPolynomial.C y₀⁻¹) with hp'
    have hid : kk * MvPolynomial.aeval (gen q) p = (J - X0) * MvPolynomial.aeval (gen q) p' := by
      have hexp : MvPolynomial.aeval (gen q) p =
          MvPolynomial.aeval (gen q) (c 0) * (J - X0) + MvPolynomial.aeval (gen q) (c 1) * (Jq - Y0) +
          MvPolynomial.aeval (gen q) (c 2) * (J⁻¹ - X0⁻¹) + MvPolynomial.aeval (gen q) (c 3) * (Jq⁻¹ - Y0⁻¹) := by
        conv_lhs => rw [hc]
        simp only [Fin.sum_univ_four, map_add, map_mul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
          gen_zero, gen_one, gen_two, gen_three, pt_zero, pt_one, pt_two, pt_three, map_inv₀]
        rw [← hJ, ← hJq, ← hX0, ← hY0]
      have hexp' : MvPolynomial.aeval (gen q) p' =
          MvPolynomial.aeval (gen q) (c 0) * kk - MvPolynomial.aeval (gen q) (c 1) * dd -
          MvPolynomial.aeval (gen q) (c 2) * (kk * J⁻¹ * X0⁻¹) + MvPolynomial.aeval (gen q) (c 3) * (dd * Jq⁻¹ * Y0⁻¹) := by
        rw [hp']
        simp only [map_add, map_mul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, gen_two, gen_three,
          map_inv₀]
        rfl
      rw [hexp, hexp']
      linear_combination (MvPolynomial.aeval (gen q) (c 0)) * h0 + (MvPolynomial.aeval (gen q) (c 1)) * h1 +
        (MvPolynomial.aeval (gen q) (c 2)) * h2 + (MvPolynomial.aeval (gen q) (c 3)) * h3
    set a := MvPolynomial.aeval (gen q) p with ha
    set a' := MvPolynomial.aeval (gen q) p' with ha'
    have ha'0 : a' ≠ 0 := by
      intro h0'
      rw [h0', mul_zero] at hid
      exact (mul_ne_zero hk0 hp) hid

    have hoW := congrArg W.ord hid
    have hoW' := congrArg W'.ord hid
    rw [W.ord_mul hk0 hp, W.ord_mul hjx ha'0, hordk, zero_add] at hoW
    rw [W'.ord_mul hk0 hp, W'.ord_mul hjx ha'0, hordk', zero_add] at hoW'

    have ha'mem : a' ∈ W'.toValuationSubring := (hasValue_aeval _ _ hgen' p').mem
    have hnn' : 0 ≤ W'.ord a' := W'.ord_nonneg_of_mem ha'mem
    have hnn : 0 ≤ W'.ord a := W'.ord_nonneg_of_mem (hasValue_aeval _ _ hgen' p).mem
    have hlt : (W'.ord a').toNat < n := by
      rw [← hn]
      have : W'.ord a' < W'.ord a := by rw [hoW']; linarith
      omega
    have IH' := IH _ hlt p' ha'0 rfl
    rw [← ha'] at IH'
    linear_combination e' * hoW - e * hoW' + IH'
  ·
    have hv := hasValue_aeval (gen q) (pt x₀ y₀) hgen p
    have hv' := hasValue_aeval (gen q) (pt x₀ y₀) hgen' p
    rw [hv.ord_eq_zero hpt, hv'.ord_eq_zero hpt, mul_zero, mul_zero]

end Induction
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun.CuspUniq"

omit [Fact q.Prime] in

theorem adjoin_coeffEmb_image_adjoin (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) :
    IntermediateField.adjoin L (coeffEmb L '' (IntermediateField.adjoin ℚ S : Set (LaurentSeries ℚ)))
      = IntermediateField.adjoin L (coeffEmb L '' S) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
    | algebraMap c =>
      rw [ModularCurve.algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
        ← algebraMap_laurentSeries_eq_single]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  · exact IntermediateField.adjoin.mono L _ _ (Set.image_mono (IntermediateField.subset_adjoin ℚ S))

theorem modularFunctionFieldBar_le_adjoin_pair :
    modularFunctionFieldBar (1 * q) ≤ IntermediateField.adjoin ℚbar
      {coeffEmb ℚbar jq, coeffEmb ℚbar (qExpand ℚ (1 * q) jq)} := by
  show laurentBaseChange ℚbar (modularFunctionFieldFull (1 * q)) ≤ _
  rw [laurentBaseChange, modularFunctionFieldFull, adjoin_coeffEmb_image_adjoin, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨d, hne, hdN, rfl⟩, rfl⟩
  haveI := hne
  have hq : q.Prime := Fact.out
  rw [Nat.one_mul] at hdN
  rcases (Nat.dvd_prime hq).mp hdN with rfl | rfl
  · rw [qExpand_one_apply]
    exact IntermediateField.subset_adjoin ℚbar _ (Set.mem_insert _ _)
  · rw [show qExpand ℚ d jq = qExpand ℚ (1 * d) jq from (qExpand_congr (Nat.one_mul d) jq).symm]
    exact IntermediateField.subset_adjoin ℚbar _ (Set.mem_insert_of_mem _ rfl)

theorem coeffEmb_jq_ne_coeffEmb_qExpand :
    coeffEmb ℚbar jq ≠ coeffEmb ℚbar (qExpand ℚ (1 * q) jq) := by
  intro h
  have h1 := congrArg (fun f : LaurentSeries ℚbar => f.coeff (-1)) h
  simp only [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  rw [qExpand_coeff_of_not_dvd (R := ℚ) (N := 1 * q) (f := jq) (by
      rw [Nat.one_mul]; intro ⟨c, hc⟩
      have : (q : ℤ) ∣ 1 := ⟨-c, by linarith⟩
      have := Int.eq_one_of_dvd_one (by positivity) this
      omega), map_zero] at h1
  exact one_ne_zero h1

theorem exists_eq_div (f : FF) :
    ∃ pa pb : MvPolynomial (Fin 4) ℚbar,
      f = MvPolynomial.aeval (gen q) pa / MvPolynomial.aeval (gen q) pb := by
  classical
  set J := coeffEmb ℚbar jq with hJ
  set Jq := coeffEmb ℚbar (qExpand ℚ (1 * q) jq) with hJq
  have hf : (f : LaurentSeries ℚbar) ∈ IntermediateField.adjoin ℚbar ({J, Jq} : Set (LaurentSeries ℚbar)) :=
    modularFunctionFieldBar_le_adjoin_pair f.2
  rw [IntermediateField.mem_adjoin_iff] at hf
  obtain ⟨r, s, hrs⟩ := hf

  let ι : (({J, Jq} : Set (LaurentSeries ℚbar))) → Fin 4 := fun x => if (x : LaurentSeries ℚbar) = J then 0 else 1
  have hι : ∀ x : ({J, Jq} : Set (LaurentSeries ℚbar)),
      (x : LaurentSeries ℚbar) = ((gen q (ι x) : FF) : LaurentSeries ℚbar) := by
    rintro ⟨x, hxm⟩
    rcases hxm with rfl | hxm
    · simp only [ι, if_pos rfl, gen_zero]; rfl
    · rw [Set.mem_singleton_iff] at hxm
      subst hxm
      have hne := coeffEmb_jq_ne_coeffEmb_qExpand (q := q)
      simp only [ι]
      rw [if_neg (Ne.symm hne), gen_one]
      rfl
  have hval : ∀ t : MvPolynomial ({J, Jq} : Set (LaurentSeries ℚbar)) ℚbar,
      MvPolynomial.aeval (fun x : ({J, Jq} : Set (LaurentSeries ℚbar)) => (x : LaurentSeries ℚbar)) t =
        ((MvPolynomial.aeval (gen q) (MvPolynomial.rename ι t) : FF) : LaurentSeries ℚbar) := by
    intro t
    rw [MvPolynomial.aeval_rename]
    have : (fun x : ({J, Jq} : Set (LaurentSeries ℚbar)) => (x : LaurentSeries ℚbar)) =
        fun x => ((modularFunctionFieldBar (1 * q)).val) ((gen q ∘ ι) x) := by
      funext x; exact hι x
    rw [this, ← MvPolynomial.comp_aeval]
    rfl
  refine ⟨MvPolynomial.rename ι r, MvPolynomial.rename ι s, ?_⟩
  apply Subtype.val_injective
  rw [hrs, hval r, hval s]
  push_cast
  rfl

theorem eq_of_isInftySide_of_hasValue (P : PlaceSpecialization A q 1 data hKr k red hα hβ) {W W' : Place ℚbar FF}
    (hW : P.IsInftySide W) (hW' : P.IsInftySide W') {x₀ : ℚbar}
    (hx : W.HasValue (jFun (q := q)) x₀) (hx' : W'.HasValue (jFun (q := q)) x₀) : W = W' := by
  set e := W.ord (jFun (q := q) - algebraMap ℚbar FF x₀) with he
  set e' := W'.ord (jFun (q := q) - algebraMap ℚbar FF x₀) with he'
  have he0 : 0 < e := ord_jFun_sub_pos' hx
  have he0' : 0 < e' := ord_jFun_sub_pos' hx'

  have hprop : ∀ f : FF, f ≠ 0 → e' * W.ord f = e * W'.ord f := by
    intro f hf
    obtain ⟨pa, pb, hfab⟩ := exists_eq_div (q := q) f
    have ha : MvPolynomial.aeval (gen q) pa ≠ 0 := by
      intro h0; rw [h0, zero_div] at hfab; exact hf hfab
    have hb : MvPolynomial.aeval (gen q) pb ≠ 0 := by
      intro h0; rw [h0, div_zero] at hfab; exact hf hfab
    have h1 := ord_aeval_proportional P hW hW' hx hx' pa ha
    have h2 := ord_aeval_proportional P hW hW' hx hx' pb hb
    rw [hfab, div_eq_mul_inv, W.ord_mul ha (inv_ne_zero hb), W'.ord_mul ha (inv_ne_zero hb), W.ord_inv, W'.ord_inv]
    linear_combination h1 - h2
  apply Place.ext
  ext f
  rcases eq_or_ne f 0 with rfl | hf
  · simp [zero_mem]
  rw [show f ∈ W.toValuationSubring ↔ 0 ≤ W.ord f from ⟨W.ord_nonneg_of_mem, W.mem_of_ord_nonneg hf⟩,
    show f ∈ W'.toValuationSubring ↔ 0 ≤ W'.ord f from ⟨W'.ord_nonneg_of_mem, W'.mem_of_ord_nonneg hf⟩]
  have h := hprop f hf
  constructor
  · intro h0
    have : 0 ≤ e * W'.ord f := by rw [← h]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith [this]) he0 |> fun h => by nlinarith [this, he0]
  · intro h0
    have : 0 ≤ e' * W.ord f := by rw [h]; positivity
    nlinarith [this, he0']

end CuspUniq
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun.CuspUniq"

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : P.IsInftySide W) (hW' : P.IsInftySide W') {x₀ : AlgebraicClosure ℚ}
    (hx : W.HasValue (PlaceSpecialization.jFun (q := q)) x₀)
    (hx' : W'.HasValue (PlaceSpecialization.jFun (q := q)) x₀) :
    W = W' :=
  CuspUniq.eq_of_isInftySide_of_hasValue P hW hW' hx hx'

end
end S_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun (solution)
