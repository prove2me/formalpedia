-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.coreCertificate_of_fixedSupport
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:45.689352+00:00
-- url     : https://prove2.me/submissions/3d7e3d64-01a2-4383-8bb5-03edc32c0ac3

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace FP5FixedSupport

open MvPolynomial HodgeComputer.FourPlusTwoResidual
open scoped BigOperators

section FractionDerivation
variable {P F : Type*} [CommRing P] [IsDomain P] [Field F]
  [Algebra P F] [IsFractionRing P F]

private def num (x : F) : P := Classical.choose (IsFractionRing.div_surjective P x)
private def den (x : F) : P := Classical.choose (Classical.choose_spec (IsFractionRing.div_surjective P x))
private lemma den_mem (x : F) : den (P := P) x ∈ nonZeroDivisors P :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).1
private lemma repr_eq (x : F) :
    algebraMap P F (num x) / algebraMap P F (den x) = x :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).2
private lemma den_ne (x : F) : algebraMap P F (den x) ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den_mem x)
private lemma map_ne {x : P} (hx : x ≠ 0) : algebraMap P F x ≠ 0 :=
  fun h => hx ((IsFractionRing.injective P F) (by simpa using h))

private def quotientD (D : Derivation ℤ P P) (x : F) : F :=
  (algebraMap P F (D (num x)) * algebraMap P F (den x) -
    algebraMap P F (num x) * algebraMap P F (D (den x))) /
    algebraMap P F (den x) ^ 2

private lemma quotientD_div (D : Derivation ℤ P P) (a b : P) (hb : b ≠ 0) :
    quotientD D (algebraMap P F a / algebraMap P F b) =
      (algebraMap P F (D a) * algebraMap P F b -
        algebraMap P F a * algebraMap P F (D b)) / algebraMap P F b ^ 2 := by
  let x := algebraMap P F a / algebraMap P F b
  have hd := den_ne (P := P) x
  have hb' := map_ne (F := F) hb
  have hcross : num x * b = a * den x := by
    apply IsFractionRing.injective P F
    simpa only [map_mul] using (div_eq_div_iff hd hb').mp (repr_eq (P := P) x)
  have hdcross := congrArg (fun p : P => algebraMap P F (D p)) hcross
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul] at hdcross
  have hcross' := congrArg (algebraMap P F) hcross
  simp only [map_mul] at hcross'
  change (algebraMap P F (D (num x)) * algebraMap P F (den x) -
    algebraMap P F (num x) * algebraMap P F (D (den x))) /
    algebraMap P F (den x) ^ 2 = _
  field_simp
  linear_combination
    algebraMap P F (den x) * algebraMap P F b * hdcross -
    (algebraMap P F b * algebraMap P F (D (den x)) +
      algebraMap P F (den x) * algebraMap P F (D b)) * hcross'

private lemma quotientD_map (D : Derivation ℤ P P) (a : P) :
    quotientD D (algebraMap P F a) = algebraMap P F (D a) := by
  have h := quotientD_div (F := F) D a 1 one_ne_zero
  simpa using h

private lemma quotientD_add (D : Derivation ℤ P P) (x y : F) :
    quotientD D (x + y) = quotientD D x + quotientD D y := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := map_ne (F := F) hb0
  have hd' := map_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b + algebraMap P F c / algebraMap P F d =
      algebraMap P F (a * d + c * b) / algebraMap P F (b * d) := by
    simp only [map_add, map_mul]; field_simp
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0,
    quotientD_div D _ _ hd0]
  simp only [map_add, map_mul, Derivation.leibniz, smul_eq_mul]
  field_simp <;> ring

private lemma quotientD_mul (D : Derivation ℤ P P) (x y : F) :
    quotientD D (x * y) = x * quotientD D y + y * quotientD D x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := map_ne (F := F) hb0
  have hd' := map_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b * (algebraMap P F c / algebraMap P F d) =
      algebraMap P F (a * c) / algebraMap P F (b * d) := by
    simp only [map_mul, mul_div_mul_comm]
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0,
    quotientD_div D _ _ hd0]
  simp only [map_mul, Derivation.leibniz, map_add, smul_eq_mul]
  field_simp <;> ring

def extendDeriv (D : Derivation ℤ P P) : Derivation ℤ F F :=
  Derivation.mk'
    ({ toFun := quotientD D
       map_zero' := by simpa using quotientD_map (F := F) D 0
       map_add' := quotientD_add D } : F →+ F).toIntLinearMap
    (fun x y => quotientD_mul D x y)

lemma extendDeriv_map (D : Derivation ℤ P P) (a : P) :
    extendDeriv (F := F) D (algebraMap P F a) = algebraMap P F (D a) :=
  quotientD_map D a

end FractionDerivation

section EvalChain
variable {k K σ : Type*} [Field k] [Field K] [CharZero k] [Fintype σ] [DecidableEq σ]

lemma derivation_eval₂_chain (D : Derivation ℤ K K) (φ : k →+* K) (x : σ → K)
    (hC : ∀ c, D (φ c) = 0) (p : MvPolynomial σ k) :
    D (eval₂Hom φ x p) = ∑ j, eval₂Hom φ x (pderiv j p) * D (x j) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp [hC c]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    simp only [map_mul, eval₂Hom_X', Derivation.leibniz, smul_eq_mul, hp,
      pderiv_mul, pderiv_X, map_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    have hpi : ∑ j, eval₂Hom φ x p * eval₂Hom φ x (Pi.single (M := fun _ => MvPolynomial σ k) j 1 i) * D (x j) =
        eval₂Hom φ x p * D (x i) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [Pi.single_eq_of_ne hji.symm]
      · intro hi; exact False.elim (hi (Finset.mem_univ i))
    rw [hpi]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring

lemma pderiv_degree_lt (p : MvPolynomial σ k) (i : σ) (hp : 0 < p.totalDegree) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  rw [totalDegree, Finset.sup_lt_iff hp]
  intro m hm
  have hcoeff : coeff (m + Finsupp.single i 1) p ≠ 0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact (mul_ne_zero_iff.mp h).1
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hs : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index] <;> simp
  rw [hs] at hd; omega

lemma constant_of_partials_zero (p : MvPolynomial σ k)
    (h : ∀ i, pderiv i p = 0) : p = C (coeff 0 p) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m; simp
  · rw [coeff_C, if_neg (Ne.symm hm)]
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra! hn; exact hm (Finsupp.ext hn)
    have hs : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
      Finsupp.sub_add_single_one_cancel hi
    have hc := congrArg (coeff (m - Finsupp.single i 1)) (h i)
    rw [coeff_pderiv, hs, coeff_zero] at hc
    have hz : (((m - Finsupp.single i 1 : σ →₀ ℕ) i) : k) + 1 ≠ 0 :=
      Nat.cast_add_one_ne_zero _
    exact (mul_eq_zero.mp hc).resolve_right hz

lemma injective_of_coordinate_derivations (φ : k →+* K) (x : σ → K)
    (D : σ → Derivation ℤ K K) (hC : ∀ i c, D i (φ c) = 0)
    (hx : ∀ i j, D i (x j) = if j = i then 1 else 0) :
    Function.Injective (eval₂Hom φ x) := by
  classical
  have compatible : ∀ i p, D i (eval₂Hom φ x p) = eval₂Hom φ x (pderiv i p) := by
    intro i p
    rw [derivation_eval₂_chain (D i) φ x (hC i) p]
    simp [hx]
  have hz : ∀ p : MvPolynomial σ k, eval₂Hom φ x p = 0 → p = 0 := by
    intro p
    induction hn : p.totalDegree using Nat.strong_induction_on generalizing p with
    | h n ih =>
      intro hzero
      have hconst : p = C (coeff 0 p) := by
        by_cases hn0 : n = 0
        · exact totalDegree_eq_zero_iff_eq_C.mp (hn.trans hn0)
        · apply constant_of_partials_zero
          intro i
          apply ih (pderiv i p).totalDegree
          · rw [← hn]; exact pderiv_degree_lt p i (by omega)
          · rfl
          · rw [← compatible, hzero, map_zero]
      rw [hconst, eval₂Hom_C] at hzero
      have hc : coeff 0 p = 0 := φ.injective (by simpa using hzero)
      rw [hconst, hc, map_zero]
  exact (injective_iff_map_eq_zero _).mpr hz

end EvalChain

section Extraction
variable {R σ : Type*} [CommRing R]

def HasOrder (n : ℕ) (p : MvPolynomial σ R) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < n → coeff m p = 0

lemma HasOrder.mono {n k : ℕ} {p : MvPolynomial σ R}
    (h : HasOrder n p) (hk : k ≤ n) : HasOrder k p :=
  fun m hm => h m (lt_of_lt_of_le hm hk)

lemma hasOrder_zero_degree (p : MvPolynomial σ R) : HasOrder 0 p :=
  fun _ hm => by omega

lemma HasOrder.add {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p + q) :=
  fun m hm => by simp [coeff_add, hp m hm, hq m hm]

lemma HasOrder.sub {n : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder n q) : HasOrder n (p - q) :=
  fun m hm => by simp [coeff_sub, hp m hm, hq m hm]

lemma HasOrder.sum {ι : Type*} (s : Finset ι) {n : ℕ}
    (p : ι → MvPolynomial σ R) (hp : ∀ i ∈ s, HasOrder n (p i)) :
    HasOrder n (∑ i ∈ s, p i) := by
  intro m hm; simp only [coeff_sum]; exact Finset.sum_eq_zero fun i hi => hp i hi m hm

lemma HasOrder.mul {n k : ℕ} {p q : MvPolynomial σ R}
    (hp : HasOrder n p) (hq : HasOrder k q) : HasOrder (n + k) (p * q) := by
  classical
  intro m hm; rw [coeff_mul]; apply Finset.sum_eq_zero; intro a ha
  have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp ha)
  simp only [map_add] at he
  by_cases h : a.1.degree < n
  · rw [hp _ h, zero_mul]
  · have h' : a.2.degree < k := by omega
    rw [hq _ h', mul_zero]

lemma HasOrder.pow {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (k : ℕ) : HasOrder (k * n) (p ^ k) := by
  induction k with
  | zero => simpa using hasOrder_zero_degree (1 : MvPolynomial σ R)
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hp

lemma HasOrder.pderiv {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (i : σ) : HasOrder (n - 1) (pderiv i p) := by
  intro m hm; rw [coeff_pderiv]
  have hd : (m + Finsupp.single i 1).degree < n := by
    simp only [map_add, Finsupp.degree_single]; omega
  rw [hp _ hd, zero_mul]

lemma isHomogeneous_hasOrder {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) : HasOrder n p :=
  fun _ hm => hp.coeff_eq_zero (ne_of_lt hm)

lemma HasOrder.component_eq_zero {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) {k : ℕ} (hk : k < n) : homogeneousComponent k p = 0 := by
  classical
  ext m; rw [coeff_homogeneousComponent]
  split_ifs with h
  · exact hp m (h ▸ hk)
  · rfl

lemma hasOrder_of_components_zero {n : ℕ} {p : MvPolynomial σ R}
    (hp : ∀ k < n, homogeneousComponent k p = 0) : HasOrder n p := by
  intro m hm
  have h := congrArg (coeff m) (hp m.degree hm)
  simpa [coeff_homogeneousComponent] using h

lemma pderiv_component (n : ℕ) (p : MvPolynomial σ R) (i : σ) :
    pderiv i (homogeneousComponent (n + 1) p) = homogeneousComponent n (pderiv i p) := by
  classical
  ext m
  simp only [coeff_pderiv, coeff_homogeneousComponent, map_add,
    Finsupp.degree_single, Nat.add_right_cancel_iff, ite_mul, zero_mul]

lemma component_mul_homogeneous {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (k : ℕ) (q : MvPolynomial σ R) :
    homogeneousComponent (n + k) (p * q) = p * homogeneousComponent k q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    have hm : (monomial m a : MvPolynomial σ R).IsHomogeneous m.degree :=
      isHomogeneous_monomial _ rfl
    rw [homogeneousComponent_of_mem (hp.mul hm), homogeneousComponent_of_mem hm]
    simp only [Nat.add_left_cancel_iff]; split_ifs <;> simp
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]

lemma pderiv_isHomogeneous {n : ℕ} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous (n + 1)) (i : σ) : (pderiv i p).IsHomogeneous n := by
  have h := pderiv_component n p i
  rw [homogeneousComponent_eq_self hp] at h; rw [h]
  exact homogeneousComponent_isHomogeneous n _

lemma order_sub_initial {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) : HasOrder (n + 1) (homogeneousComponent n p - p) := by
  classical
  intro m hm; rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : m.degree = n
  · simp [h]
  · have hlt : m.degree < n := by omega
    simp [h, hp _ hlt]

variable [Fintype σ]

def polynomialDirectional (p : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := ∑ i, N i * pderiv i p

def polynomialDivergence (N : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, pderiv i (N i)

def polynomialDivNum (D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := D * polynomialDivergence N - polynomialDirectional D N

lemma polynomialDirectional_mul (p q : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    polynomialDirectional (p * q) N =
      p * polynomialDirectional q N + q * polynomialDirectional p N := by
  simp only [polynomialDirectional, pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  conv_rhs => rw [add_comm]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma polynomialDirectional_scale (p S : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    polynomialDirectional p (fun i => S * N i) = S * polynomialDirectional p N := by
  simp only [polynomialDirectional, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma polynomialDivergence_scale (S : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    polynomialDivergence (fun i => S * N i) =
      polynomialDirectional S N + S * polynomialDivergence N := by
  simp only [polynomialDivergence, polynomialDirectional, pderiv_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro i _; ring

lemma component_polynomialDivNum {d : ℕ} {H : MvPolynomial σ R}
    (hd : 0 < d) (hH : H.IsHomogeneous d) (N : σ → MvPolynomial σ R) :
    homogeneousComponent (2 * d) (polynomialDivNum H N) =
      polynomialDivNum H (fun i => homogeneousComponent (d + 1) (N i)) := by
  have hderiv (i : σ) : (pderiv i H).IsHomogeneous (d - 1) := by
    apply pderiv_isHomogeneous
    have he : d - 1 + 1 = d := by omega
    simpa only [he] using hH
  simp only [polynomialDivNum, polynomialDivergence, polynomialDirectional, map_sub, map_sum]
  rw [show 2 * d = d + d by omega, component_mul_homogeneous hH]
  simp only [map_sum, ← pderiv_component]
  congr 1; apply Finset.sum_congr rfl; intro i _
  rw [mul_comm (N i), show d + d = (d - 1) + (d + 1) by omega,
    component_mul_homogeneous (hderiv i)]; ring

lemma component_polynomialDirectional {f d : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous (f + 1)) (N : σ → MvPolynomial σ R) :
    homogeneousComponent (f + d) (polynomialDirectional F N) =
      polynomialDirectional F (fun i => homogeneousComponent d (N i)) := by
  simp only [polynomialDirectional, map_sum]; apply Finset.sum_congr rfl; intro i _
  rw [mul_comm (N i), component_mul_homogeneous (pderiv_isHomogeneous hF i)]; ring

def finiteInverse (D h : MvPolynomial σ R) (p : ℕ) : MvPolynomial σ R :=
  ∑ i ∈ Finset.range p, h ^ i * (h - D) ^ (p - 1 - i)

omit [Fintype σ] in
lemma finiteInverse_identity (D h : MvPolynomial σ R) (p : ℕ) :
    D * finiteInverse D h p = h ^ p - (h - D) ^ p := by
  rw [mul_comm]; simpa only [finiteInverse, sub_sub_cancel] using geom_sum₂_mul h (h - D) p

abbrev CorePoly := MvPolynomial (Fin 4) ℂ

lemma core_hom : core.IsHomogeneous 6 := by
  have hX := isHomogeneous_X (σ := Fin 4) ℂ
  have hC := isHomogeneous_C (Fin 4) (R := ℂ)
  have t1 : (X 0 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 0).pow 6
  have t2 : (C (5 / 7 : ℂ) * X 0 ^ 5 * X 1 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 0).pow 5)).mul (hX 1)
  have t3 : (C (5 / 7 : ℂ) * X 0 ^ 3 * X 1 * X 2 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((((hC _).mul ((hX 0).pow 3)).mul (hX 1)).mul (hX 2)).mul (hX 3)
  have t4 : (C (10 / 7 : ℂ) * X 0 * X 1 ^ 5 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul (hX 0)).mul ((hX 1).pow 5)
  have t5 : (C (10 / 7 : ℂ) * X 0 * X 1 * X 2 ^ 3 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((((hC _).mul (hX 0)).mul (hX 1)).mul ((hX 2).pow 3)).mul (hX 3)
  have t6 : (X 1 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 1).pow 6
  have t7 : (X 2 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 2).pow 6
  have t8 : (C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul ((hX 2).pow 5)).mul (hX 3)
  have t9 : (C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 : CorePoly).IsHomogeneous 6 :=
    ((hC _).mul (hX 2)).mul ((hX 3).pow 5)
  have t10 : (X 3 ^ 6 : CorePoly).IsHomogeneous 6 := (hX 3).pow 6
  unfold core
  exact ((((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).add t10

def defect (D : CorePoly) (N : Fin 4 → CorePoly) : CorePoly :=
  2 • (coreSource * D ^ 2) - 2 • (D * polynomialDirectional core N) +
    3 • (core * polynomialDivNum D N)

lemma defect_scale (D S : CorePoly) (N : Fin 4 → CorePoly) :
    defect (S * D) (fun i => S * N i) = S ^ 2 * defect D N := by
  simp only [defect, polynomialDivNum, polynomialDirectional_scale,
    polynomialDivergence_scale, polynomialDirectional_mul, nsmul_eq_mul]; ring

lemma defect_change (T U : CorePoly) (M : Fin 4 → CorePoly) :
    defect (T - U) M = defect T M +
      (2 • (coreSource * U * (U - 2 * T)) + 2 • (U * polynomialDirectional core M) +
        3 • (core * (polynomialDirectional U M - U * polynomialDivergence M))) := by
  have hd : polynomialDirectional (T - U) M = polynomialDirectional T M - polynomialDirectional U M := by
    simp only [polynomialDirectional, map_sub, mul_sub, Finset.sum_sub_distrib]
  simp only [defect, polynomialDivNum, hd, nsmul_eq_mul]; ring

lemma scaled_order {n : ℕ} {Q : CorePoly} (h : HasOrder n Q) (c : ℕ) :
    HasOrder n (c • Q) := by
  rw [nsmul_eq_mul]; simpa using (hasOrder_zero_degree (c : CorePoly)).mul h

lemma directional_order {n w : ℕ} {P : CorePoly} {M : Fin 4 → CorePoly}
    (hP : HasOrder n P) (hM : ∀ i, HasOrder w (M i)) :
    HasOrder (w + (n - 1)) (polynomialDirectional P M) :=
  HasOrder.sum _ _ fun i _ => (hM i).mul (hP.pderiv i)

lemma inverse_order (D : CorePoly) (d p : ℕ) (hD : HasOrder d D) :
    HasOrder ((p - 1) * d) (finiteInverse D (homogeneousComponent d D) p) := by
  let h := homogeneousComponent d D
  have hh : HasOrder d h := isHomogeneous_hasOrder (homogeneousComponent_isHomogeneous d D)
  have hR : HasOrder d (h - D) := hh.sub hD
  apply HasOrder.sum; intro i hi
  have hip := Finset.mem_range.mp hi
  have hsum : i + (p - 1 - i) = p - 1 := by omega
  simpa only [h, ← Nat.add_mul, hsum] using (hh.pow i).mul (hR.pow (p - 1 - i))

lemma least_component (D : CorePoly) (hne : D ≠ 0) :
    ∃ d, HasOrder d D ∧ homogeneousComponent d D ≠ 0 := by
  classical
  have hex : ∃ n, homogeneousComponent n D ≠ 0 := by
    by_contra! hall; apply hne; rw [← sum_homogeneousComponent D]
    exact Finset.sum_eq_zero (fun k _ => hall k)
  exact ⟨Nat.find hex, hasOrder_of_components_zero (fun k hk => not_ne_iff.mp (Nat.find_min hex hk)),
    Nat.find_spec hex⟩

lemma source_hom : coreSource.IsHomogeneous 6 :=
  ((isHomogeneous_X ℂ (0 : Fin 4)).pow 3).mul ((isHomogeneous_X ℂ (2 : Fin 4)).pow 3)

lemma defect_component (T : CorePoly) (M : Fin 4 → CorePoly) (e : ℕ)
    (he : 0 < e) (hT : T.IsHomogeneous e) :
    homogeneousComponent (2 * e + 6) (defect T M) =
      defect T (fun i => homogeneousComponent (e + 1) (M i)) := by
  have hA : (coreSource * T ^ 2).IsHomogeneous (2 * e + 6) := by
    convert source_hom.mul (hT.pow 2) using 1; omega
  have hdir : homogeneousComponent (2 * e + 6) (T * polynomialDirectional core M) =
      T * polynomialDirectional core (fun i => homogeneousComponent (e + 1) (M i)) := by
    rw [show 2 * e + 6 = e + (5 + (e + 1)) by omega, component_mul_homogeneous hT,
      component_polynomialDirectional (show core.IsHomogeneous (5 + 1) from core_hom)]
  have hdiv : homogeneousComponent (2 * e + 6) (core * polynomialDivNum T M) =
      core * polynomialDivNum T (fun i => homogeneousComponent (e + 1) (M i)) := by
    rw [show 2 * e + 6 = 6 + 2 * e by omega, component_mul_homogeneous core_hom,
      component_polynomialDivNum he hT]
  simp only [defect, map_add, map_sub, map_nsmul, homogeneousComponent_eq_self hA, hdir, hdiv]

lemma project_initial (D : CorePoly) (N : Fin 4 → CorePoly) (d : ℕ)
    (hd : 0 < d) (hD : HasOrder d D) (h0 : homogeneousComponent d D ≠ 0)
    (hc : defect D N = 0) : ∃ T M, CoreCertificate T M := by
  let h := homogeneousComponent d D
  let p := d + 2
  let e := p * d
  let u := p * (d + 1)
  let w := (p - 1) * d
  let T := h ^ p
  let U := (h - D) ^ p
  let S := finiteInverse D h p
  let M : Fin 4 → CorePoly := fun i => S * N i
  have hp : 0 < p := by dsimp [p]; omega
  have he : 0 < e := Nat.mul_pos hp hd
  have hu : u = e + (d + 2) := by simp only [u, e, p, Nat.mul_add, Nat.mul_one]
  have hw : w + d = e := by
    dsimp only [w, e, p]; rw [show d + 2 - 1 = d + 1 by omega, ← Nat.succ_mul]
  have hh := homogeneousComponent_isHomogeneous d D
  have hT : T.IsHomogeneous e := by simpa only [T, h, e, Nat.mul_comm] using hh.pow p
  have tOrd := isHomogeneous_hasOrder hT
  have uOrd : HasOrder u U := (order_sub_initial hD).pow p
  have mOrd (i : Fin 4) : HasOrder w (M i) := by
    simpa only [Nat.add_zero, M, S, h, w] using
      (inverse_order D d p hD).mul (hasOrder_zero_degree (N i))
  have divOrd : HasOrder (w - 1) (polynomialDivergence M) :=
    HasOrder.sum _ _ (fun i _ => (mOrd i).pderiv i)
  have hErr1 : HasOrder (2 * e + 7) (coreSource * U * (U - 2 * T)) := by
    have hUT : HasOrder e (U - 2 * T) := by
      apply HasOrder.sub (uOrd.mono (by omega))
      simpa only [two_nsmul, two_mul] using tOrd.add tOrd
    apply ((isHomogeneous_hasOrder source_hom).mul uOrd |>.mul hUT).mono; omega
  have hErr2 : HasOrder (2 * e + 7) (U * polynomialDirectional core M) := by
    apply (uOrd.mul (directional_order (isHomogeneous_hasOrder core_hom) mOrd)).mono; omega
  have hErr3 : HasOrder (2 * e + 1) (polynomialDirectional U M) := by
    apply (directional_order uOrd mOrd).mono; omega
  have hErr4 : HasOrder (2 * e + 1) (U * polynomialDivergence M) := by
    apply (uOrd.mul divOrd).mono; omega
  have hErr5 : HasOrder (2 * e + 7) (core * (polynomialDirectional U M - U * polynomialDivergence M)) :=
    ((isHomogeneous_hasOrder core_hom).mul (hErr3.sub hErr4)).mono (by omega)
  have hz := (((scaled_order hErr1 2).add (scaled_order hErr2 2)).add (scaled_order hErr5 3)).component_eq_zero
    (k := 2 * e + 6) (by omega)
  have hscaled : defect (T - U) M = 0 := by
    have hds : D * S = T - U := finiteInverse_identity D h p
    rw [← hds, mul_comm D S, show M = (fun i => S * N i) from rfl, defect_scale, hc, mul_zero]
  rw [defect_change] at hscaled
  have hproj := congrArg (homogeneousComponent (2 * e + 6)) hscaled
  rw [map_add, hz, add_zero, map_zero, defect_component T M e he hT] at hproj
  refine ⟨T, (fun i => homogeneousComponent (e + 1) (M i)), pow_ne_zero p h0, ⟨e - 1, ?_, ?_⟩, ?_⟩
  · simpa only [show e - 1 + 1 = e by omega] using hT
  · intro i
    simpa only [show e - 1 + 2 = e + 1 by omega] using homogeneousComponent_isHomogeneous (e + 1) (M i)
  · simpa only [defect, nsmul_eq_mul, Nat.cast_ofNat, polynomialDivNum, polynomialDirectional,
      polynomialDivergence, mul_comm, mul_left_comm, mul_assoc] using hproj

theorem core_of_ungraded (D : CorePoly) (N : Fin 4 → CorePoly) (hD : D ≠ 0)
    (hraw : 2 * coreSource * D ^ 2 - 2 * D * (∑ i, pderiv i core * N i)
      + 3 * core * (D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i) = 0) :
    ∃ T M, CoreCertificate T M := by
  have hc : defect D N = 0 := by
    simpa only [defect, nsmul_eq_mul, Nat.cast_ofNat, polynomialDivNum, polynomialDirectional,
      polynomialDivergence, mul_comm, mul_left_comm, mul_assoc] using hraw
  let x : CorePoly := X 0
  obtain ⟨d, ho, hn⟩ := least_component (x * D) (mul_ne_zero (X_ne_zero 0) hD)
  have hOrd1 : HasOrder 1 (x * D) := by
    simpa only [Nat.add_zero] using
      (isHomogeneous_hasOrder (isHomogeneous_X ℂ (0 : Fin 4))).mul (hasOrder_zero_degree D)
  have hd : 0 < d := by
    by_contra! hv; exact hn (hOrd1.component_eq_zero (by omega))
  exact project_initial (x * D) (fun i => x * N i) d hd ho hn (by rw [defect_scale, hc, mul_zero])

theorem core_of_rational {K : Type*} [Field K] [CharZero K]
    [Algebra CorePoly K] [IsFractionRing CorePoly K]
    (δ : Fin 4 → Derivation ℤ K K)
    (hδ : ∀ i p, δ i (algebraMap CorePoly K p) = algebraMap CorePoly K (pderiv i p))
    (v : Fin 4 → K) (hsource : CoreRationalEquation δ v) :
    ∃ T M, CoreCertificate T M := by
  classical
  let φ := algebraMap CorePoly K
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors CorePoly) v
  choose N hN using hd
  let D : CorePoly := d
  have hD : D ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hv (i : Fin 4) : φ (N i) = φ D * v i := by simpa only [Algebra.smul_def] using hN i
  have hv' (i : Fin 4) : φ (pderiv i (N i)) = φ D * δ i (v i) + v i * φ (pderiv i D) := by
    have hi := congrArg (δ i) (hv i)
    simpa only [φ, hδ, Derivation.leibniz, smul_eq_mul] using hi
  have hn : (∑ i, φ (pderiv i core) * φ (N i)) = φ D * ∑ i, v i * δ i (φ core) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [hv i, show δ i (φ core) = φ (pderiv i core) from hδ i _]; ring
  have hc : (∑ i, φ (pderiv i D) * φ (N i)) = φ D * ∑ i, v i * φ (pderiv i D) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [hv i]; ring
  have hdiv : φ D * (∑ i, φ (pderiv i (N i))) - (∑ i, φ (pderiv i D) * φ (N i)) =
      (φ D) ^ 2 * ∑ i, δ i (v i) := by
    simp only [hv', Finset.sum_add_distrib, ← Finset.mul_sum, hc]; ring
  apply core_of_ungraded D N hD
  apply IsFractionRing.injective CorePoly K
  change φ _ = φ 0
  simp only [map_add, map_sub, map_mul, map_pow, map_sum, map_ofNat, map_zero, hn, hdiv]
  unfold CoreRationalEquation at hsource
  change (∑ i, v i * δ i (φ core)) - (3 / 2 : K) * φ core * (∑ i, δ i (v i)) = φ coreSource at hsource
  linear_combination -2 * (φ D) ^ 2 * hsource

end Extraction

section AffineLift

abbrev AffinePoly := MvPolynomial (Fin 3) ℂ

private lemma d_div_pow {K : Type*} [Field K] (D : Derivation ℤ K K)
    (x y : K) (n : ℕ) (hy : y ≠ 0) :
    D (x / y ^ n) = (y * D x - (n : K) * x * D y) / y ^ (n + 1) := by
  cases n with
  | zero => simp [hy]
  | succ m =>
    rw [Derivation.leibniz_div, Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.succ_sub_one, Nat.cast_succ, pow_succ]
    field_simp [hy] <;> ring

private lemma affine_equation {K : Type*} [Field K] [CharZero K]
    (θ : AffinePoly →+* K) (E : Fin 3 → Derivation ℤ K K)
    (compat : ∀ i p, E i (θ p) = θ (pderiv i p))
    (B : AffinePoly) (n : ℕ) (N : Fin 3 → AffinePoly) (hb : θ B ≠ 0)
    (hraw : FixedSupportEquation B n N) :
    let q : Fin 3 → K := fun i => θ (N i) / (θ B) ^ n
    2 * (∑ i, q i * E i (θ affineCore)) - 3 * θ affineCore * (∑ i, E i (q i)) = 3 * θ (X 1) ^ 3 := by
  intro q
  have hmul : (θ B) ^ (n + 1) * (∑ i, q i * E i (θ affineCore)) =
      θ B * (∑ i, θ (N i) * θ (pderiv i affineCore)) := by
    rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    dsimp only [q]; rw [compat, pow_succ]; field_simp [hb]
  have hdiv : (θ B) ^ (n + 1) * (∑ i, E i (q i)) =
      θ B * (∑ i, θ (pderiv i (N i))) - (n : K) * (∑ i, θ (N i) * θ (pderiv i B)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
    dsimp only [q]; rw [d_div_pow _ _ _ _ hb, compat, compat]; field_simp [hb]
  have h := congrArg θ hraw
  simp only [map_sub, map_mul, map_sum, map_pow, map_ofNat, map_natCast] at h
  apply mul_left_cancel₀ (pow_ne_zero (n + 1) hb)
  linear_combination h + 2 * hmul - 3 * θ affineCore * hdiv

private lemma chart_identity {K : Type*} [Field K]
    (φ : CorePoly →+* K) (a : K) (ha : a ≠ 0) (haφ : a = φ (X 0)) :
    let x := fun i : Fin 3 => φ (X i.succ) / a
    let θ := eval₂Hom (φ.comp C) x
    φ core = a ^ 6 * θ affineCore ∧ φ coreSource = a ^ 6 * (θ (X 1)) ^ 3 := by
  intro x θ
  constructor <;>
    simp only [core, affineCore, coreSource, θ, x, map_add, map_mul, map_pow, map_one,
      eval₂Hom_X', eval₂Hom_C, RingHom.comp_apply, ← haφ, show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (1 : Fin 3).succ = (2 : Fin 4) from rfl, show (2 : Fin 3).succ = (3 : Fin 4) from rfl] <;>
    field_simp [ha] <;> ring

end AffineLift
end FP5FixedSupport

private lemma solution_in_field
    {K : Type} [Field K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    [IsFractionRing (MvPolynomial (Fin 4) ℂ) K]
    (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ)
    (hB : B ≠ 0) (hraw : HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N) :
    ∃ (T : MvPolynomial (Fin 4) ℂ) (M : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificate T M := by
  classical
  haveI : CharZero K := ⟨fun m n h => by
    apply Nat.cast_injective (R := ℂ)
    apply MvPolynomial.C_injective (Fin 4) ℂ
    apply IsFractionRing.injective (MvPolynomial (Fin 4) ℂ) K
    simpa only [map_natCast] using h⟩
  let δ : Fin 4 → Derivation ℤ K K := fun i =>
    FP5FixedSupport.extendDeriv (P := MvPolynomial (Fin 4) ℂ) (F := K)
      ((MvPolynomial.pderiv i : Derivation ℂ (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ)).restrictScalars ℤ)
  have hδ : ∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
      δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
        algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p) := fun i p =>
    FP5FixedSupport.extendDeriv_map (P := MvPolynomial (Fin 4) ℂ) (F := K)
      ((MvPolynomial.pderiv i : Derivation ℂ (MvPolynomial (Fin 4) ℂ) (MvPolynomial (Fin 4) ℂ)).restrictScalars ℤ) p
  let φ := algebraMap (MvPolynomial (Fin 4) ℂ) K
  let a := φ (MvPolynomial.X 0)
  let x := fun i : Fin 3 => φ (MvPolynomial.X i.succ) / a
  let θ := MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) x
  let E : Fin 3 → Derivation ℤ K K := fun i => a • δ i.succ
  have ha : a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin 4)))
  have hDa (i : Fin 3) : δ i.succ a = 0 := by
    dsimp [a, φ]; rw [hδ]; simp [MvPolynomial.pderiv_X]
  have hDc (i j : Fin 3) : δ i.succ (φ (MvPolynomial.X j.succ)) = if j = i then 1 else 0 := by
    dsimp [φ]; rw [hδ]; simp only [MvPolynomial.pderiv_X]; split <;> simp_all
  have hC (i : Fin 3) (c : ℂ) : E i ((φ.comp MvPolynomial.C) c) = 0 := by
    change a * (δ i.succ) ((algebraMap (MvPolynomial (Fin 4) ℂ) K) (MvPolynomial.C c)) = 0
    rw [hδ]; simp
  have hx (i j : Fin 3) : E i (x j) = if j = i then 1 else 0 := by
    change a * (δ i.succ) (φ (MvPolynomial.X j.succ) / a) = if j = i then 1 else 0
    rw [Derivation.leibniz_div, hDa, hDc]
    split
    · subst_vars
      simp only [smul_eq_mul, mul_zero, sub_zero, one_mul, div_eq_mul_inv]
      calc
        _ = a ^ 2 * (a ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 ha)
    · simp
  have hθ (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) : E i (θ p) = θ (MvPolynomial.pderiv i p) := by
    change E i ((MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) x) p) =
      (MvPolynomial.eval₂Hom (φ.comp MvPolynomial.C) x) (MvPolynomial.pderiv i p)
    rw [FP5FixedSupport.derivation_eval₂_chain (E i) (φ.comp MvPolynomial.C) x (hC i) p]
    simp [hx]
  have hinj := FP5FixedSupport.injective_of_coordinate_derivations (φ.comp MvPolynomial.C) x E hC hx
  have hb : θ B ≠ 0 := fun hz => hB (hinj (by simpa only [map_zero] using hz))
  let q := fun i : Fin 3 => θ (N i) / (θ B) ^ n
  have hq := FP5FixedSupport.affine_equation θ E hθ B n N hb hraw
  change 2 * (∑ i, q i * E i (θ HodgeComputer.FourPlusTwoResidual.affineCore)) -
    3 * θ HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, E i (q i)) =
    3 * θ (MvPolynomial.X 1) ^ 3 at hq
  obtain ⟨hH, hA⟩ := FP5FixedSupport.chart_identity φ a ha rfl
  change φ HodgeComputer.FourPlusTwoResidual.core =
    a ^ 6 * θ HodgeComputer.FourPlusTwoResidual.affineCore at hH
  change φ HodgeComputer.FourPlusTwoResidual.coreSource =
    a ^ 6 * θ (MvPolynomial.X 1) ^ 3 at hA
  let v : Fin 4 → K := Fin.cases 0 (fun i => (2 / 3 : K) * a * q i)
  have hdir : (∑ j, v j * δ j (φ HodgeComputer.FourPlusTwoResidual.core)) =
      (2 / 3 : K) * a ^ 6 * ∑ i, q i * E i (θ HodgeComputer.FourPlusTwoResidual.affineCore) := by
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    simp only [v, Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add]
    apply Finset.sum_congr rfl; intro i _
    rw [hH, Derivation.leibniz, Derivation.leibniz_pow, hDa]
    simp only [E, Derivation.smul_apply, smul_eq_mul, mul_zero]; ring
  have h23 (i : Fin 3) : δ i.succ (2 / 3 : K) = 0 := by
    rw [Derivation.leibniz_div, show δ i.succ (2 : K) = 0 from (δ i.succ).map_natCast 2,
      show δ i.succ (3 : K) = 0 from (δ i.succ).map_natCast 3]; simp
  have hdiv : (∑ j, δ j (v j)) = (2 / 3 : K) * ∑ i, E i (q i) := by
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    simp only [v, Fin.cases_zero, Fin.cases_succ, map_zero, zero_add]
    apply Finset.sum_congr rfl; intro i _
    simp only [Derivation.leibniz, h23, hDa, smul_eq_mul, E, Derivation.smul_apply, mul_zero, add_zero]
    ring
  apply FP5FixedSupport.core_of_rational δ hδ v
  unfold HodgeComputer.FourPlusTwoResidual.CoreRationalEquation
  change (∑ j, v j * δ j (φ HodgeComputer.FourPlusTwoResidual.core)) -
    (3 / 2 : K) * φ HodgeComputer.FourPlusTwoResidual.core * (∑ j, δ j (v j)) =
    φ HodgeComputer.FourPlusTwoResidual.coreSource
  rw [hdir, hdiv, hH, hA]
  linear_combination (a ^ 6 / 3) * hq

theorem solution :
    ∀ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 →
      HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N →
      ∃ (T : MvPolynomial (Fin 4) ℂ) (M : Fin 4 → MvPolynomial (Fin 4) ℂ),
        HodgeComputer.FourPlusTwoResidual.CoreCertificate T M := by
  intro B n N hB hraw
  exact solution_in_field (K := FractionRing (MvPolynomial (Fin 4) ℂ)) B n N hB hraw
