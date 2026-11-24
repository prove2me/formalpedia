-- Prove2me | solution 1 for HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:27:14.258567+00:00
-- url     : https://prove2.me/submissions/04dfc9e8-eec1-4c0d-b567-860a8bacd448

import Definitions.Def_HodgeComputerFormal_PolyEncoding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000

section
/-! Exact positional encoding of polynomials with natural coefficients.
Evaluation at b is injective when each polynomial has coefficient sum less
than b. The bound is essential: a successful numerical evaluation without it
does not prove a polynomial identity. Prepared with OpenAI Codex assistance. -/
namespace PolynomialEncoding.PolynomialDigits
open Polynomial

lemma eval_divX (p : Polynomial ℕ) (b : ℕ) :
    p.eval b=p.divX.eval b*b+p.coeff 0 := by
  conv_lhs => rw [← divX_mul_X_add p]
  simp

lemma coeff_zero_le_eval_one (p : Polynomial ℕ) : p.coeff 0≤p.eval 1 := by
  rw [eval_divX]
  omega

lemma divX_eval_one_le (p : Polynomial ℕ) : p.divX.eval 1≤p.eval 1 := by
  rw [eval_divX p]
  simp only [mul_one]
  omega

lemma eval_eq_implies_constant_eq (b : ℕ) (p q : Polynomial ℕ)
    (hp : p.eval 1<b) (hq : q.eval 1<b) (he : p.eval b=q.eval b) :
    p.coeff 0=q.coeff 0 := by
  have hp0 := (coeff_zero_le_eval_one p).trans_lt hp
  have hq0 := (coeff_zero_le_eval_one q).trans_lt hq
  have hm := congrArg (fun n => n%b) he
  rw [eval_divX p,eval_divX q] at hm
  simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_add,
    Nat.mod_eq_of_lt hp0,Nat.mod_eq_of_lt hq0,Nat.mod_mod,Nat.zero_mod] using hm

theorem eval_injective_bounded (b : ℕ) (hb : 0<b) (p q : Polynomial ℕ)
    (hp : p.eval 1<b) (hq : q.eval 1<b) (he : p.eval b=q.eval b) : p=q := by
  suffices h : ∀ n (p q : Polynomial ℕ),p.natDegree≤n → q.natDegree≤n →
      p.eval 1<b → q.eval 1<b → p.eval b=q.eval b → p=q by
    exact h (max p.natDegree q.natDegree) p q (le_max_left ..) (le_max_right ..) hp hq he
  intro n
  induction n with
  | zero =>
    intro p q hpd hqd hp hq he
    have hpC := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hpd)
    have hqC := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hqd)
    rw [hpC,hqC] at he ⊢
    simpa using he
  | succ n ih =>
    intro p q hpd hqd hp hq he
    have hc := eval_eq_implies_constant_eq b p q hp hq he
    have hd : p.divX.eval b=q.divX.eval b := by
      rw [eval_divX p,eval_divX q,hc] at he
      exact Nat.eq_of_mul_eq_mul_right hb (Nat.add_right_cancel he)
    have hdiv : p.divX=q.divX := by
      apply ih
      · rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      · rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      · exact (divX_eval_one_le p).trans_lt hp
      · exact (divX_eval_one_le q).trans_lt hq
      · exact hd
    calc
      p=p.divX*X+C (p.coeff 0) := (divX_mul_X_add p).symm
      _=q.divX*X+C (q.coeff 0) := by rw [hdiv,hc]
      _=q := divX_mul_X_add q

end PolynomialEncoding.PolynomialDigits

end

noncomputable section
namespace PolynomialEncoding.KroneckerCheck
open MvPolynomial Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open scoped BigOperators Polynomial
def stride {n : ℕ} (bound : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∏ j : Fin n, if j.val < i.val then bound j else 1

/-- Mixed-radix index of a monomial exponent vector `m : Fin n →₀ ℕ`. -/
def monIdx {n : ℕ} (bound : Fin n → ℕ) (m : Fin n →₀ ℕ) : ℕ :=
  ∑ i : Fin n, m i * stride bound i

lemma stride_succ {n : ℕ} (bound : Fin (n + 1) → ℕ) (i : Fin n) :
    stride bound i.succ = bound 0 * stride (fun j => bound j.succ) i := by
  simp [stride, Fin.prod_univ_succ]

lemma stride_zero {n : ℕ} (bound : Fin (n + 1) → ℕ) : stride bound 0 = 1 := by
  simp [stride]

lemma monIdx_injective : ∀ {n : ℕ} (bound : Fin n → ℕ) (m₁ m₂ : Fin n →₀ ℕ),
    (∀ i, m₁ i < bound i) → (∀ i, m₂ i < bound i) →
    monIdx bound m₁ = monIdx bound m₂ → m₁ = m₂
  | 0, _, m₁, m₂, _, _, _ => by ext i; exact Fin.elim0 i
  | n + 1, bound, m₁, m₂, h₁, h₂, heq => by
    have hsum (m : Fin (n + 1) →₀ ℕ) :
        monIdx bound m = m 0 + bound 0 *
          monIdx (fun j : Fin n => bound j.succ) (Finsupp.equivFunOnFinite.symm (fun j => m j.succ)) := by
      simp only [monIdx, Fin.sum_univ_succ, stride_zero, mul_one, stride_succ]
      rw [Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro j _
      change m j.succ * (bound 0 * stride (fun j => bound j.succ) j) =
        bound 0 * (m j.succ * stride (fun j => bound j.succ) j)
      ring
    rw [hsum m₁, hsum m₂] at heq
    have h0 : m₁ 0 = m₂ 0 := by
      have hm := congrArg (· % bound 0) heq
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (h₁ 0), Nat.mod_eq_of_lt (h₂ 0)] at hm
      exact hm
    have hb0 : 0 < bound 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) (h₁ 0)
    have htail_eq :
        monIdx (fun j : Fin n => bound j.succ) (Finsupp.equivFunOnFinite.symm (fun j => m₁ j.succ)) =
        monIdx (fun j : Fin n => bound j.succ) (Finsupp.equivFunOnFinite.symm (fun j => m₂ j.succ)) := by
      rw [h0] at heq
      exact Nat.eq_of_mul_eq_mul_left hb0 (Nat.add_left_cancel heq)
    have htail := monIdx_injective (fun j : Fin n => bound j.succ)
      (Finsupp.equivFunOnFinite.symm (fun j => m₁ j.succ))
      (Finsupp.equivFunOnFinite.symm (fun j => m₂ j.succ))
      (fun j => by simpa using h₁ j.succ) (fun j => by simpa using h₂ j.succ) htail_eq
    ext i
    refine Fin.cases h0 (fun j => ?_) i
    simpa using congrArg (fun f : Fin n →₀ ℕ => f j) htail

/-- Kronecker encoding homomorphism `MvPolynomial (Fin n) ℕ →+* ℕ[X]`. -/
def encode {n : ℕ} (bound : Fin n → ℕ) : MvPolynomial (Fin n) ℕ →+* ℕ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.X ^ stride bound i)

lemma encode_monomial {n : ℕ} (bound : Fin n → ℕ) (m : Fin n →₀ ℕ) (c : ℕ) :
    encode bound (monomial m c) = Polynomial.monomial (monIdx bound m) c := by
  rw [encode, eval₂Hom_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  rw [Finsupp.prod_of_support_subset m (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, monIdx]
  congr 1; apply Finset.sum_congr rfl; intro i _; ring

lemma encode_coeff_of_bounded {n : ℕ} (bound : Fin n → ℕ) (p : MvPolynomial (Fin n) ℕ)
    (hp : ∀ m ∈ p.support, ∀ i, m i < bound i) (m₀ : Fin n →₀ ℕ) (hm₀ : ∀ i, m₀ i < bound i) :
    (encode bound p).coeff (monIdx bound m₀) = p.coeff m₀ := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [encode_monomial, Polynomial.coeff_monomial]
  by_cases hmem : m₀ ∈ p.support
  · rw [Finset.sum_eq_single m₀]
    · simp
    · intro m hm hne
      have hidx : monIdx bound m ≠ monIdx bound m₀ := fun h =>
        hne (monIdx_injective bound m m₀ (hp m hm) hm₀ h)
      simp [hidx]
    · intro h; exact (h hmem).elim
  · rw [Finset.sum_eq_zero]
    · exact (MvPolynomial.notMem_support_iff.mp hmem).symm
    · intro m hm
      have hne : m ≠ m₀ := fun h => hmem (h ▸ hm)
      have hidx : monIdx bound m ≠ monIdx bound m₀ := fun h =>
        hne (monIdx_injective bound m m₀ (hp m hm) hm₀ h)
      simp [hidx]

theorem encode_injective_of_bounded {n : ℕ} (bound : Fin n → ℕ) (p q : MvPolynomial (Fin n) ℕ)
    (hp : ∀ m ∈ p.support, ∀ i, m i < bound i)
    (hq : ∀ m ∈ q.support, ∀ i, m i < bound i)
    (heq : encode bound p = encode bound q) : p = q := by
  ext m
  by_cases hm : ∀ i, m i < bound i
  · rw [← encode_coeff_of_bounded bound p hp m hm,
      ← encode_coeff_of_bounded bound q hq m hm, heq]
  · have h1 : m ∉ p.support := fun h => hm (hp m h)
    have h2 : m ∉ q.support := fun h => hm (hq m h)
    rw [MvPolynomial.notMem_support_iff.mp h1, MvPolynomial.notMem_support_iff.mp h2]

def polyVar (n : ℕ) (i : ℕ) : MvPolynomial (Fin n) ℕ :=
  if h : i < n then MvPolynomial.X ⟨i, h⟩ else 0

lemma deg_le_add {n : ℕ} {p q : MvPolynomial (Fin n) ℕ} {d₁ d₂ : Fin n → ℕ}
    (hp : ∀ m ∈ p.support, ∀ i, m i ≤ d₁ i)
    (hq : ∀ m ∈ q.support, ∀ i, m i ≤ d₂ i) :
    ∀ m ∈ (p + q).support, ∀ i, m i ≤ max (d₁ i) (d₂ i) := by
  intro m hm i
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact (hp m h i).trans (le_max_left _ _)
  · exact (hq m h i).trans (le_max_right _ _)

lemma deg_le_mul {n : ℕ} {p q : MvPolynomial (Fin n) ℕ} {d₁ d₂ : Fin n → ℕ}
    (hp : ∀ m ∈ p.support, ∀ i, m i ≤ d₁ i)
    (hq : ∀ m ∈ q.support, ∀ i, m i ≤ d₂ i) :
    ∀ m ∈ (p * q).support, ∀ i, m i ≤ d₁ i + d₂ i := by
  intro m hm i
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simpa only [Finsupp.add_apply] using Nat.add_le_add (hp m₁ hm₁ i) (hq m₂ hm₂ i)

lemma deg_le_pairMul {n : ℕ} {p q : MvPolynomial (Fin n) ℕ × MvPolynomial (Fin n) ℕ}
    {d₁ d₂ : Fin n → ℕ}
    (hp : (∀ m ∈ p.1.support, ∀ i, m i ≤ d₁ i) ∧ (∀ m ∈ p.2.support, ∀ i, m i ≤ d₁ i))
    (hq : (∀ m ∈ q.1.support, ∀ i, m i ≤ d₂ i) ∧ (∀ m ∈ q.2.support, ∀ i, m i ≤ d₂ i)) :
    (∀ m ∈ (pairMul p q).1.support, ∀ i, m i ≤ d₁ i + d₂ i) ∧
    (∀ m ∈ (pairMul p q).2.support, ∀ i, m i ≤ d₁ i + d₂ i) := by
  constructor
  · simpa [pairMul] using deg_le_add (deg_le_mul hp.1 hq.1) (deg_le_mul hp.2 hq.2)
  · simpa [pairMul] using deg_le_add (deg_le_mul hp.1 hq.2) (deg_le_mul hp.2 hq.1)

lemma support_natCast_eq_zero {n : ℕ} (k : ℕ) {m : Fin n →₀ ℕ}
    (hm : m ∈ (k : MvPolynomial (Fin n) ℕ).support) : m = 0 := by
  rw [MvPolynomial.mem_support_iff, ← map_natCast MvPolynomial.C, MvPolynomial.coeff_C] at hm
  by_contra h
  exact hm (if_neg (Ne.symm h))

lemma deg_le_pairPow {n : ℕ} {p : MvPolynomial (Fin n) ℕ × MvPolynomial (Fin n) ℕ}
    {d : Fin n → ℕ}
    (hp : (∀ m ∈ p.1.support, ∀ i, m i ≤ d i) ∧ (∀ m ∈ p.2.support, ∀ i, m i ≤ d i)) :
    ∀ k : ℕ,
      (∀ m ∈ (pairPow p k).1.support, ∀ i, m i ≤ k * d i) ∧
      (∀ m ∈ (pairPow p k).2.support, ∀ i, m i ≤ k * d i)
  | 0 => by
    constructor
    · intro m hm i
      have h0 : m = 0 := support_natCast_eq_zero 1 (by simpa [pairPow] using hm)
      subst h0; simp
    · intro m hm; simp [pairPow] at hm
  | k + 1 => by
    have ih := deg_le_pairPow hp k
    have hmul := deg_le_pairMul hp ih
    constructor
    · intro m hm i
      have := hmul.1 m hm i
      simpa [Nat.succ_mul, Nat.add_comm] using this
    · intro m hm i
      have := hmul.2 m hm i
      simpa [Nat.succ_mul, Nat.add_comm] using this

lemma splitEval_deg_le (n : ℕ) (e : Expr) :
    (∀ m ∈ (splitEval (polyVar n) e).1.support, ∀ i : Fin n, m i ≤ exprDeg i.val e) ∧
    (∀ m ∈ (splitEval (polyVar n) e).2.support, ∀ i : Fin n, m i ≤ exprDeg i.val e) := by
  induction e with
  | num k =>
    cases k with
    | ofNat a =>
      constructor
      · intro m hm i
        have h0 := support_natCast_eq_zero a (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
      · intro m hm; simp [splitEval, numberPair] at hm
    | negSucc a =>
      constructor
      · intro m hm; simp [splitEval, numberPair] at hm
      · intro m hm i
        have h0 := support_natCast_eq_zero (a + 1) (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
  | intCast k =>
    cases k with
    | ofNat a =>
      constructor
      · intro m hm i
        have h0 := support_natCast_eq_zero a (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
      · intro m hm; simp [splitEval, numberPair] at hm
    | negSucc a =>
      constructor
      · intro m hm; simp [splitEval, numberPair] at hm
      · intro m hm i
        have h0 := support_natCast_eq_zero (a + 1) (by simpa [splitEval, numberPair] using hm)
        subst h0; simp [exprDeg]
  | natCast k =>
    constructor
    · intro m hm i
      have h0 := support_natCast_eq_zero k (by simpa [splitEval] using hm)
      subst h0; simp [exprDeg]
    · intro m hm; simp [splitEval] at hm
  | var j =>
    constructor
    · intro m hm i
      dsimp only [splitEval, polyVar] at hm
      split_ifs at hm with hj
      · rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
        subst hm
        simp only [Finsupp.single_apply, exprDeg]
        by_cases hji : j = i.val
        · subst hji; simp
        · have hne : (⟨j, hj⟩ : Fin n) ≠ i := fun h => hji (congrArg Fin.val h)
          simp [hne, hji]
      · simp at hm
    · intro m hm; simp [splitEval] at hm
  | neg a ih => exact ⟨ih.2, ih.1⟩
  | add a b iha ihb =>
    exact ⟨deg_le_add iha.1 ihb.1, deg_le_add iha.2 ihb.2⟩
  | sub a b iha ihb =>
    exact ⟨deg_le_add iha.1 ihb.2, deg_le_add iha.2 ihb.1⟩
  | mul a b iha ihb => exact deg_le_pairMul iha ihb
  | pow a k iha => exact deg_le_pairPow iha k

def value {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (i : ℕ) : ℕ :=
  if h : i < n then b ^ stride bound ⟨i, h⟩ else 0

def evaluation {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) : MvPolynomial (Fin n) ℕ →+* ℕ :=
  (Polynomial.evalRingHom b).comp (encode bound)

lemma evaluation_polyVar {n : ℕ} (bound : Fin n → ℕ) (b i : ℕ) :
    evaluation bound b (polyVar n i) = value bound b i := by
  dsimp only [evaluation, encode, polyVar, value]
  split_ifs with h <;> simp

lemma evaluation_parts {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (e : Expr) :
    (evaluation bound b (splitEval (polyVar n) e).1,
     evaluation bound b (splitEval (polyVar n) e).2) =
      splitEval (value bound b) e := by
  simpa only [evaluation_polyVar] using splitEval_map (evaluation bound b) (polyVar n) e

lemma value_one {n : ℕ} (bound : Fin n → ℕ) (i : ℕ) :
    value bound 1 i = if i < n then 1 else 0 := by
  dsimp only [value]; split_ifs <;> simp

def positiveMass (n : ℕ) (e f : Expr) : ℕ :=
  (splitEval (fun i => if i < n then 1 else 0) e).1 +
    (splitEval (fun i => if i < n then 1 else 0) f).2

def negativeMass (n : ℕ) (e f : Expr) : ℕ :=
  (splitEval (fun i => if i < n then 1 else 0) f).1 +
    (splitEval (fun i => if i < n then 1 else 0) e).2

lemma cast_parts {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (e : Expr) :
    ((splitEval (value bound b) e).1 : ℤ) - (splitEval (value bound b) e).2 =
      ringEval (fun i => (value bound b i : ℤ)) e := by
  have h' := splitEval_map (Nat.castRingHom ℤ) (value bound b) e
  change (((splitEval (value bound b) e).1 : ℤ), ((splitEval (value bound b) e).2 : ℤ)) =
    splitEval (fun i => (value bound b i : ℤ)) e at h'
  have hd := splitEval_difference (fun i => (value bound b i : ℤ)) e
  rw [← h'] at hd
  exact hd

lemma ringEval_congr_varsInRange {K : Type*} [CommRing K]
    (n : ℕ) (v₁ v₂ : ℕ → K) (hv : ∀ i < n, v₁ i = v₂ i) :
    ∀ e : Expr, varsInRange n e = true → ringEval v₁ e = ringEval v₂ e
  | .num _, _ => rfl
  | .natCast _, _ => rfl
  | .intCast _, _ => rfl
  | .var i, h => hv i (of_decide_eq_true h)
  | .neg a, h => congrArg (-·) (ringEval_congr_varsInRange n v₁ v₂ hv a h)
  | .add a b, h => by
    simp only [varsInRange, Bool.and_eq_true] at h
    simp [ringEval, ringEval_congr_varsInRange n v₁ v₂ hv a h.1,
      ringEval_congr_varsInRange n v₁ v₂ hv b h.2]
  | .sub a b, h => by
    simp only [varsInRange, Bool.and_eq_true] at h
    simp [ringEval, ringEval_congr_varsInRange n v₁ v₂ hv a h.1,
      ringEval_congr_varsInRange n v₁ v₂ hv b h.2]
  | .mul a b, h => by
    simp only [varsInRange, Bool.and_eq_true] at h
    simp [ringEval, ringEval_congr_varsInRange n v₁ v₂ hv a h.1,
      ringEval_congr_varsInRange n v₁ v₂ hv b h.2]
  | .pow a k, h => congrArg (· ^ k) (ringEval_congr_varsInRange n v₁ v₂ hv a h)

theorem encoded_identity {n : ℕ} (bound : Fin n → ℕ) (b : ℕ) (e f : Expr)
    (hb : 0 < b)
    (hde : ∀ i : Fin n, exprDeg i.val e < bound i)
    (hdf : ∀ i : Fin n, exprDeg i.val f < bound i)
    (hp : positiveMass n e f < b) (hn : negativeMass n e f < b)
    (hnum : ringEval (fun i => (value bound b i : ℤ)) e =
      ringEval (fun i => (value bound b i : ℤ)) f) :
    (splitEval (polyVar n) e).1 + (splitEval (polyVar n) f).2 =
      (splitEval (polyVar n) f).1 + (splitEval (polyVar n) e).2 := by
  let p := (splitEval (polyVar n) e).1 + (splitEval (polyVar n) f).2
  let q := (splitEval (polyVar n) f).1 + (splitEval (polyVar n) e).2
  have heD := splitEval_deg_le n e
  have hfD := splitEval_deg_le n f
  apply encode_injective_of_bounded bound p q
  · intro m hm i
    exact (deg_le_add heD.1 hfD.2 m hm i).trans_lt (max_lt (hde i) (hdf i))
  · intro m hm i
    exact (deg_le_add hfD.1 heD.2 m hm i).trans_lt (max_lt (hdf i) (hde i))
  apply PolynomialEncoding.PolynomialDigits.eval_injective_bounded b hb
  · change evaluation bound 1 p < b
    have he1 := congrArg Prod.fst (evaluation_parts bound 1 e)
    have hf2 := congrArg Prod.snd (evaluation_parts bound 1 f)
    dsimp only at he1 hf2
    have hv1 : value bound 1 = (fun i => if i < n then 1 else 0) := funext (value_one bound)
    rw [hv1] at he1 hf2
    simpa only [p, map_add, he1, hf2, positiveMass] using hp
  · change evaluation bound 1 q < b
    have hf1 := congrArg Prod.fst (evaluation_parts bound 1 f)
    have he2 := congrArg Prod.snd (evaluation_parts bound 1 e)
    dsimp only at hf1 he2
    have hv1 : value bound 1 = (fun i => if i < n then 1 else 0) := funext (value_one bound)
    rw [hv1] at hf1 he2
    simpa only [q, map_add, hf1, he2, negativeMass] using hn
  · change evaluation bound b p = evaluation bound b q
    have he1 := congrArg Prod.fst (evaluation_parts bound b e)
    have he2 := congrArg Prod.snd (evaluation_parts bound b e)
    have hf1 := congrArg Prod.fst (evaluation_parts bound b f)
    have hf2 := congrArg Prod.snd (evaluation_parts bound b f)
    dsimp only at he1 he2 hf1 hf2
    simp only [p, q, map_add, he1, he2, hf1, hf2]
    rw [← cast_parts, ← cast_parts] at hnum
    omega

theorem identity_of_kronecker {K : Type*} [CommRing K]
    {n : ℕ} (v : ℕ → K) (bound : Fin n → ℕ) (b : ℕ) (e f : Expr)
    (hb : 0 < b)
    (hve : varsInRange n e = true) (hvf : varsInRange n f = true)
    (hde : ∀ i : Fin n, exprDeg i.val e < bound i)
    (hdf : ∀ i : Fin n, exprDeg i.val f < bound i)
    (hp : positiveMass n e f < b) (hn : negativeMass n e f < b)
    (hnum : ringEval (fun i => (value bound b i : ℤ)) e =
      ringEval (fun i => (value bound b i : ℤ)) f) :
    ringEval v e = ringEval v f := by
  let v' : ℕ → K := fun i => if i < n then v i else 0
  have hv (i : ℕ) (hi : i < n) : v i = v' i := by simp [v', hi]
  rw [ringEval_congr_varsInRange n v v' hv e hve,
      ringEval_congr_varsInRange n v v' hv f hvf]
  let φ : MvPolynomial (Fin n) ℕ →+* K := eval₂Hom (Nat.castRingHom K) (fun i : Fin n => v i.val)
  have hvar (i : ℕ) : φ (polyVar n i) = v' i := by
    dsimp only [φ, polyVar, v']; split_ifs <;> simp
  have h := congrArg φ (encoded_identity bound b e f hb hde hdf hp hn hnum)
  rw [map_add, map_add] at h
  have he' := splitEval_map φ (polyVar n) e
  have hf' := splitEval_map φ (polyVar n) f
  have heDiff := splitEval_difference (fun i => φ (polyVar n i)) e
  have hfDiff := splitEval_difference (fun i => φ (polyVar n i)) f
  rw [← he'] at heDiff
  rw [← hf'] at hfDiff
  simp only [hvar] at heDiff hfDiff
  rw [← heDiff, ← hfDiff]
  linear_combination h

/-! Hybrid Kronecker + small-integer grid checker:
Kronecker-encodes the first `m` variables (`0 .. m-1`) and evaluates the last `k` variables
(`m .. m+k-1`) on `{0, ..., gridDeg j}`. Keeps Kronecker bit-widths tiny even for high-degree
5-variable polynomials while proving exact identities in any `CommRing K` via pure kernel `rfl`. -/

def allGrid : ∀ {k : ℕ}, (Fin k → ℕ) → ((Fin k → ℕ) → Bool) → Bool
  | 0, _, P => P Fin.elim0
  | _ + 1, d, P =>
    (List.range (d 0 + 1)).all fun a =>
      allGrid (fun j => d j.succ) (fun g => P (Fin.cons a g))

lemma allGrid_eq_true : ∀ {k : ℕ} (d : Fin k → ℕ) (P : (Fin k → ℕ) → Bool),
    allGrid d P = true → ∀ g : Fin k → ℕ, (∀ j, g j ≤ d j) → P g = true
  | 0, _, P, h, g, _ => by
    have hg : g = Fin.elim0 := funext fun j => Fin.elim0 j
    simpa [allGrid, hg] using h
  | _ + 1, d, P, h, g, hg => by
    rw [allGrid, List.all_eq_true] at h
    have ha : g 0 ∈ List.range (d 0 + 1) := List.mem_range.mpr (Nat.lt_succ_of_le (hg 0))
    have hrec := allGrid_eq_true (fun j => d j.succ) (fun g' => P (Fin.cons (g 0) g'))
      (h (g 0) ha) (fun j => g j.succ) (fun j => hg j.succ)
    have hcons : Fin.cons (g 0) (fun j => g j.succ) = g := by
      ext j; refine Fin.cases rfl (fun _ => rfl) j
    simpa [hcons] using hrec

def gridVal {m k : ℕ} (bound : Fin m → ℕ) (b : ℕ) (g : Fin k → ℕ) (i : ℕ) : ℕ :=
  if h1 : i < m then b ^ stride bound ⟨i, h1⟩
  else if h2 : i < m + k then g ⟨i - m, by omega⟩
  else 0

def gridMassVal {m k : ℕ} (gridDeg : Fin k → ℕ) (i : ℕ) : ℕ :=
  if h1 : i < m then 1
  else if h2 : i < m + k then gridDeg ⟨i - m, by omega⟩
  else 0

def positiveMassGrid {m k : ℕ} (gridDeg : Fin k → ℕ) (e f : Expr) : ℕ :=
  (splitEval (gridMassVal (m := m) gridDeg) e).1 +
    (splitEval (gridMassVal (m := m) gridDeg) f).2

def negativeMassGrid {m k : ℕ} (gridDeg : Fin k → ℕ) (e f : Expr) : ℕ :=
  (splitEval (gridMassVal (m := m) gridDeg) f).1 +
    (splitEval (gridMassVal (m := m) gridDeg) e).2

def checkGrid {m k : ℕ} (bound : Fin m → ℕ) (gridDeg : Fin k → ℕ) (b : ℕ) (e f : Expr) : Bool :=
  allGrid gridDeg fun g =>
    decide (ringEval (fun i => (gridVal bound b g i : ℤ)) e =
      ringEval (fun i => (gridVal bound b g i : ℤ)) f)

lemma mvpoly_eval_mono {n : ℕ} {v₁ v₂ : Fin n → ℕ} (h : ∀ i, v₁ i ≤ v₂ i)
    (p : MvPolynomial (Fin n) ℕ) : MvPolynomial.eval v₁ p ≤ MvPolynomial.eval v₂ p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add]; exact Nat.add_le_add hp hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact Nat.mul_le_mul hp (h i)

lemma mvpoly_zero_of_grid {R : Type*} [CommRing R] [IsDomain R] [CharZero R] :
    ∀ {k : ℕ} (d : Fin k → ℕ) (p : MvPolynomial (Fin k) R),
      (∀ m ∈ p.support, ∀ j, m j ≤ d j) →
      (∀ g : Fin k → ℕ, (∀ j, g j ≤ d j) → MvPolynomial.eval (fun j => (g j : R)) p = 0) →
      p = 0
  | 0, _, p, _, hzero => by
    have hp : ∀ q : MvPolynomial (Fin 0) R,
        q = MvPolynomial.C (MvPolynomial.eval (fun j : Fin 0 => ((Fin.elim0 j : ℕ) : R)) q) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C c => simp
      | add a b ha hb => rw [map_add, map_add, ← ha, ← hb]
      | mul_X _ j _ => exact Fin.elim0 j
    have h0 := hzero Fin.elim0 (fun j => Fin.elim0 j)
    rw [hp p, h0, map_zero]
  | k + 1, d, p, hdeg, hzero => by
    let P : Polynomial (MvPolynomial (Fin k) R) := MvPolynomial.finSuccEquiv R k p
    have hPdeg : P.natDegree ≤ d 0 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      ext m
      rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      simp only [MvPolynomial.coeff_zero]
      by_contra hne
      have hmem : Finsupp.cons n m ∈ p.support := MvPolynomial.mem_support_iff.mpr hne
      have hle := hdeg _ hmem 0
      simp only [Finsupp.cons_zero] at hle
      omega
    have hroot (a : ℕ) (ha : a ≤ d 0) :
        Polynomial.eval (MvPolynomial.C (a : R)) P = 0 := by
      let q := Polynomial.eval (MvPolynomial.C (a : R)) P
      apply mvpoly_zero_of_grid (fun j => d j.succ) q
      · intro m hm j
        rw [MvPolynomial.mem_support_iff] at hm
        have hq_coeff : q.coeff m =
            ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).coeff m * (a : R) ^ i := by
          dsimp only [q]
          rw [Polynomial.eval_eq_sum_range, MvPolynomial.coeff_sum]
          apply Finset.sum_congr rfl; intro i _
          rw [← map_pow, _root_.mul_comm, MvPolynomial.coeff_C_mul, _root_.mul_comm]
        rw [hq_coeff] at hm
        have hex : ∃ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).coeff m * (a : R) ^ i ≠ 0 := by
          by_contra hall; push Not at hall; exact hm (Finset.sum_eq_zero hall)
        obtain ⟨i, _, hi⟩ := hex
        have hci : (P.coeff i).coeff m ≠ 0 := left_ne_zero_of_mul hi
        rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hci
        have hle := hdeg _ (MvPolynomial.mem_support_iff.mpr hci) j.succ
        simpa only [Finsupp.cons_succ] using hle
      · intro g hg
        have heval_eq : MvPolynomial.eval (fun j => (g j : R)) (Polynomial.eval (MvPolynomial.C (a : R)) P) =
            MvPolynomial.eval (fun j => ((Fin.cons a g : Fin (k + 1) → ℕ) j : R)) p := by
          let φ₁ : MvPolynomial (Fin (k + 1)) R →+* R :=
            (MvPolynomial.eval (fun j => (g j : R))).comp
              ((Polynomial.evalRingHom (MvPolynomial.C (a : R))).comp (MvPolynomial.finSuccEquiv R k).toRingHom)
          let φ₂ : MvPolynomial (Fin (k + 1)) R →+* R :=
            MvPolynomial.eval (fun j => ((Fin.cons a g : Fin (k + 1) → ℕ) j : R))
          have hφ : φ₁ = φ₂ := by
            apply MvPolynomial.ringHom_ext
            · intro r; simp [φ₁, φ₂, MvPolynomial.finSuccEquiv_apply]
            · intro i; refine Fin.cases ?_ (fun j => ?_) i
              · simp [φ₁, φ₂, MvPolynomial.finSuccEquiv_X_zero]
              · simp [φ₁, φ₂, MvPolynomial.finSuccEquiv_X_succ]
          exact congrArg (fun f => f p) hφ
        rw [heval_eq]
        exact hzero (Fin.cons a g) (fun j => Fin.cases ha (fun j' => hg j') j)
    have hP0 : P = 0 := by
      classical
      by_contra hPne
      let S : Finset (MvPolynomial (Fin k) R) :=
        (Finset.range (d 0 + 1)).image (fun a : ℕ => MvPolynomial.C (a : R))
      have hinj : Function.Injective (fun a : ℕ => MvPolynomial.C (σ := Fin k) (a : R)) :=
        Function.Injective.comp (MvPolynomial.C_injective (Fin k) R) Nat.cast_injective
      have hScard : S.card = d 0 + 1 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      have hsub : S ⊆ P.roots.toFinset := by
        intro r hr
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
        exact hroot a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
      have hle1 : S.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      have hle2 : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      have hle3 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
      omega
    exact (MvPolynomial.finSuccEquiv R k).injective (by simpa [P] using hP0)

theorem identity_of_grid_kronecker {K : Type*} [CommRing K]
    {m k : ℕ} (v : ℕ → K) (bound : Fin m → ℕ) (gridDeg : Fin k → ℕ) (b : ℕ) (e f : Expr)
    (hb : 0 < b)
    (hve : varsInRange (m + k) e = true) (hvf : varsInRange (m + k) f = true)
    (hde_m : ∀ i : Fin m, exprDeg i.val e < bound i)
    (hdf_m : ∀ i : Fin m, exprDeg i.val f < bound i)
    (hde_k : ∀ j : Fin k, exprDeg (m + j.val) e ≤ gridDeg j)
    (hdf_k : ∀ j : Fin k, exprDeg (m + j.val) f ≤ gridDeg j)
    (hp : positiveMassGrid (m := m) gridDeg e f < b)
    (hn : negativeMassGrid (m := m) gridDeg e f < b)
    (hgrid : checkGrid bound gridDeg b e f = true) :
    ringEval v e = ringEval v f := by
  let p := (splitEval (polyVar (m + k)) e).1 + (splitEval (polyVar (m + k)) f).2
  let q := (splitEval (polyVar (m + k)) f).1 + (splitEval (polyVar (m + k)) e).2
  have heD := splitEval_deg_le (m + k) e
  have hfD := splitEval_deg_le (m + k) f
  have hp_m : ∀ mon ∈ p.support, ∀ i : Fin m, mon ⟨i.val, by omega⟩ < bound i := by
    intro mon hmon i
    exact (deg_le_add heD.1 hfD.2 mon hmon ⟨i.val, by omega⟩).trans_lt (max_lt (hde_m i) (hdf_m i))
  have hq_m : ∀ mon ∈ q.support, ∀ i : Fin m, mon ⟨i.val, by omega⟩ < bound i := by
    intro mon hmon i
    exact (deg_le_add hfD.1 heD.2 mon hmon ⟨i.val, by omega⟩).trans_lt (max_lt (hdf_m i) (hde_m i))
  have hp_k : ∀ mon ∈ p.support, ∀ j : Fin k, mon ⟨m + j.val, by omega⟩ ≤ gridDeg j := by
    intro mon hmon j
    exact (deg_le_add heD.1 hfD.2 mon hmon ⟨m + j.val, by omega⟩).trans (max_le (hde_k j) (hdf_k j))
  have hq_k : ∀ mon ∈ q.support, ∀ j : Fin k, mon ⟨m + j.val, by omega⟩ ≤ gridDeg j := by
    intro mon hmon j
    exact (deg_le_add hfD.1 heD.2 mon hmon ⟨m + j.val, by omega⟩).trans (max_le (hdf_k j) (hde_k j))
  let splitMap : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin k) (MvPolynomial (Fin m) ℤ) :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (MvPolynomial.C.comp (Nat.castRingHom ℤ)))
      (fun idx => if h : idx.val < m then MvPolynomial.C (MvPolynomial.X ⟨idx.val, h⟩)
        else MvPolynomial.X ⟨idx.val - m, by omega⟩)
  -- For every grid point g ≤ gridDeg, evG p = evG q in MvPolynomial (Fin m) ℕ!
  have hsplit_eq : splitMap p = splitMap q := by
    apply sub_eq_zero.mp
    apply mvpoly_zero_of_grid gridDeg (splitMap p - splitMap q)
    · -- Degree bound in Fin k of splitMap p - splitMap q
      have hdeg_split (r : MvPolynomial (Fin (m + k)) ℕ)
          (hr : ∀ mon ∈ r.support, ∀ j : Fin k, mon ⟨m + j.val, by omega⟩ ≤ gridDeg j) :
          ∀ mon ∈ (splitMap r).support, ∀ j : Fin k, mon j ≤ gridDeg j := by
        intro mon hmon j
        rw [r.as_sum, map_sum] at hmon
        obtain ⟨d, hd, hmem⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmon)
        dsimp only [splitMap] at hmem
        rw [eval₂Hom_monomial] at hmem
        have hprod_eq : (d.prod fun idx a =>
              (if h : idx.val < m then MvPolynomial.C (MvPolynomial.X (R := ℤ) ⟨idx.val, h⟩)
                else MvPolynomial.X ⟨idx.val - m, by omega⟩) ^ a) =
            MvPolynomial.C (∏ i : Fin m, MvPolynomial.X (R := ℤ) i ^ d ⟨i.val, by omega⟩) *
              MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun j : Fin k => d ⟨m + j.val, by omega⟩) 1 := by
          rw [Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
          rw [Fin.prod_univ_add]
          congr 1
          · rw [map_prod]
            apply Finset.prod_congr rfl; intro i _
            have hi : (Fin.castAdd k i).val < m := i.isLt
            rw [dif_pos hi, map_pow]; rfl
          · rw [MvPolynomial.monomial_eq, map_one, one_mul,
              Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
            apply Finset.prod_congr rfl; intro j _
            have hj : ¬ (Fin.natAdd m j).val < m := by simp
            rw [dif_neg hj]; simp [Fin.natAdd]
        simp only [RingHom.comp_apply] at hmem
        rw [hprod_eq, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one] at hmem
        have hmon_eq : mon = Finsupp.equivFunOnFinite.symm fun j : Fin k => d ⟨m + j.val, by omega⟩ :=
          Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmem)
        subst hmon_eq
        simpa using hr d hd j
      intro mon hmon j
      rw [sub_eq_add_neg] at hmon
      rcases Finset.mem_union.mp (MvPolynomial.support_add hmon) with h | h
      · exact hdeg_split p hp_k mon h j
      · rw [MvPolynomial.support_neg] at h; exact hdeg_split q hq_k mon h j
    · intro g hg
      let evG : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin m) ℕ :=
        MvPolynomial.eval₂Hom MvPolynomial.C
          (fun idx => if h : idx.val < m then MvPolynomial.X ⟨idx.val, h⟩
            else MvPolynomial.C (g ⟨idx.val - m, by omega⟩))
      have hevG_eq : evG p = evG q := by
        have hdeg_evG (r : MvPolynomial (Fin (m + k)) ℕ)
            (hr : ∀ mon ∈ r.support, ∀ i : Fin m, mon ⟨i.val, by omega⟩ < bound i) :
            ∀ mon ∈ (evG r).support, ∀ i : Fin m, mon i < bound i := by
          intro mon hmon i
          rw [r.as_sum, map_sum] at hmon
          obtain ⟨d, hd, hmem⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmon)
          dsimp only [evG] at hmem
          rw [eval₂Hom_monomial] at hmem
          have hprod_eq : (d.prod fun idx a =>
                (if h : idx.val < m then MvPolynomial.X (R := ℕ) ⟨idx.val, h⟩
                  else MvPolynomial.C (g ⟨idx.val - m, by omega⟩)) ^ a) =
              MvPolynomial.C (∏ j : Fin k, g j ^ d ⟨m + j.val, by omega⟩) *
                MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i : Fin m => d ⟨i.val, by omega⟩) 1 := by
            rw [Finsupp.prod_of_support_subset d (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
            rw [Fin.prod_univ_add, _root_.mul_comm]
            congr 1
            · rw [map_prod]
              apply Finset.prod_congr rfl; intro j _
              have hj : ¬ (Fin.natAdd m j).val < m := by simp
              rw [dif_neg hj, map_pow]; simp [Fin.natAdd]
            · rw [MvPolynomial.monomial_eq, map_one, one_mul,
                Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
              apply Finset.prod_congr rfl; intro i _
              have hi : (Fin.castAdd k i).val < m := i.isLt
              rw [dif_pos hi]; simp [Fin.castAdd, Fin.castLE]
          rw [hprod_eq, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one] at hmem
          have hmon_eq : mon = Finsupp.equivFunOnFinite.symm fun i : Fin m => d ⟨i.val, by omega⟩ :=
            Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hmem)
          subst hmon_eq
          simpa using hr d hd i
        apply encode_injective_of_bounded bound (evG p) (evG q) (hdeg_evG p hp_m) (hdeg_evG q hq_m)
        apply PolynomialEncoding.PolynomialDigits.eval_injective_bounded b hb
        · -- Mass bound for evG p at 1, via monotonicity from gridMassVal
          have heval1 (r : MvPolynomial (Fin (m + k)) ℕ) :
              (encode bound (evG r)).eval 1 =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) r := by
            change ((Polynomial.evalRingHom 1).comp ((encode bound).comp evG)) r = _
            have hhom : (Polynomial.evalRingHom 1).comp ((encode bound).comp evG) =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) := by
              apply MvPolynomial.ringHom_ext
              · intro c; simp [evG, encode]
              · intro idx
                simp only [RingHom.comp_apply, evG, encode, eval₂Hom_X', gridVal]
                by_cases h1 : idx.val < m
                · simp [h1]
                · simp [h1]
            exact congrArg (fun f => f r) hhom
          rw [heval1]
          have hmono : MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) p ≤
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) p := by
            apply mvpoly_eval_mono; intro idx
            dsimp only [gridVal, gridMassVal]
            by_cases h1 : idx.val < m
            · simp [h1]
            · simp only [dif_neg h1, dif_pos idx.isLt]
              exact hg ⟨idx.val - m, by omega⟩
          have hmass : MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) p =
              positiveMassGrid (m := m) gridDeg e f := by
            let evM : MvPolynomial (Fin (m + k)) ℕ →+* ℕ :=
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val)
            have hvar (i : ℕ) : evM (polyVar (m + k) i) = gridMassVal (m := m) gridDeg i := by
              dsimp only [evM, polyVar, gridMassVal]
              by_cases h2 : i < m + k
              · simp [h2]
              · have h1 : ¬ i < m := by omega
                simp [h1, h2]
            have he' := congrArg Prod.fst (splitEval_map evM (polyVar (m + k)) e)
            have hf' := congrArg Prod.snd (splitEval_map evM (polyVar (m + k)) f)
            dsimp only at he' hf'; simp only [hvar] at he' hf'
            change evM p = positiveMassGrid (m := m) gridDeg e f
            rw [show p = (splitEval (polyVar (m + k)) e).1 + (splitEval (polyVar (m + k)) f).2 from rfl,
              map_add, he', hf']; rfl
          exact hmono.trans_lt (hmass.symm ▸ hp)
        · -- Mass bound for evG q at 1
          have heval1 (r : MvPolynomial (Fin (m + k)) ℕ) :
              (encode bound (evG r)).eval 1 =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) r := by
            change ((Polynomial.evalRingHom 1).comp ((encode bound).comp evG)) r = _
            have hhom : (Polynomial.evalRingHom 1).comp ((encode bound).comp evG) =
                MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) := by
              apply MvPolynomial.ringHom_ext
              · intro c; simp [evG, encode]
              · intro idx
                simp only [RingHom.comp_apply, evG, encode, eval₂Hom_X', gridVal]
                by_cases h1 : idx.val < m
                · simp [h1]
                · simp [h1]
            exact congrArg (fun f => f r) hhom
          rw [heval1]
          have hmono : MvPolynomial.eval (fun idx : Fin (m + k) => gridVal bound 1 g idx.val) q ≤
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) q := by
            apply mvpoly_eval_mono; intro idx
            dsimp only [gridVal, gridMassVal]
            by_cases h1 : idx.val < m
            · simp [h1]
            · simp only [dif_neg h1, dif_pos idx.isLt]
              exact hg ⟨idx.val - m, by omega⟩
          have hmass : MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val) q =
              negativeMassGrid (m := m) gridDeg e f := by
            let evM : MvPolynomial (Fin (m + k)) ℕ →+* ℕ :=
              MvPolynomial.eval (fun idx : Fin (m + k) => gridMassVal (m := m) gridDeg idx.val)
            have hvar (i : ℕ) : evM (polyVar (m + k) i) = gridMassVal (m := m) gridDeg i := by
              dsimp only [evM, polyVar, gridMassVal]
              by_cases h2 : i < m + k
              · simp [h2]
              · have h1 : ¬ i < m := by omega
                simp [h1, h2]
            have hf' := congrArg Prod.fst (splitEval_map evM (polyVar (m + k)) f)
            have he' := congrArg Prod.snd (splitEval_map evM (polyVar (m + k)) e)
            dsimp only at hf' he'; simp only [hvar] at hf' he'
            change evM q = negativeMassGrid (m := m) gridDeg e f
            rw [show q = (splitEval (polyVar (m + k)) f).1 + (splitEval (polyVar (m + k)) e).2 from rfl,
              map_add, hf', he']; rfl
          exact hmono.trans_lt (hmass.symm ▸ hn)
        · -- Equality at b from hgrid!
          have hnum : ringEval (fun i => (gridVal bound b g i : ℤ)) e =
              ringEval (fun i => (gridVal bound b g i : ℤ)) f :=
            of_decide_eq_true (allGrid_eq_true gridDeg _ hgrid g hg)
          let evB : MvPolynomial (Fin (m + k)) ℕ →+* ℕ :=
            (Polynomial.evalRingHom b).comp ((encode bound).comp evG)
          have hevB_var (i : ℕ) : evB (polyVar (m + k) i) = gridVal bound b g i := by
            dsimp only [evB, polyVar, gridVal, evG, encode]
            by_cases h2 : i < m + k
            · by_cases h1 : i < m
              · simp [h1, h2]
              · simp [h1, h2]
            · have h1 : ¬ i < m := by omega
              simp [h1, h2]
          have he1 := congrArg Prod.fst (splitEval_map evB (polyVar (m + k)) e)
          have he2 := congrArg Prod.snd (splitEval_map evB (polyVar (m + k)) e)
          have hf1 := congrArg Prod.fst (splitEval_map evB (polyVar (m + k)) f)
          have hf2 := congrArg Prod.snd (splitEval_map evB (polyVar (m + k)) f)
          dsimp only at he1 he2 hf1 hf2
          have hfun : (fun i => evB (polyVar (m + k) i)) = gridVal bound b g := funext hevB_var
          rw [hfun] at he1 he2 hf1 hf2
          have hcast (expr : Expr) :
              ((splitEval (gridVal bound b g) expr).1 : ℤ) - (splitEval (gridVal bound b g) expr).2 =
                ringEval (fun i => (gridVal bound b g i : ℤ)) expr := by
            have h' := splitEval_map (Nat.castRingHom ℤ) (gridVal bound b g) expr
            change (((splitEval (gridVal bound b g) expr).1 : ℤ),
              ((splitEval (gridVal bound b g) expr).2 : ℤ)) =
              splitEval (fun i => (gridVal bound b g i : ℤ)) expr at h'
            have hd := splitEval_difference (fun i => (gridVal bound b g i : ℤ)) expr
            rw [← h'] at hd; exact hd
          change evB p = evB q
          simp only [p, q, map_add, he1, he2, hf1, hf2]
          rw [← hcast e, ← hcast f] at hnum
          omega
      -- Lift evG p = evG q to MvPolynomial (Fin m) ℤ and identify with eval g (splitMap p - splitMap q)
      have hcomm (r : MvPolynomial (Fin (m + k)) ℕ) :
          MvPolynomial.eval (fun j : Fin k => (g j : MvPolynomial (Fin m) ℤ)) (splitMap r) =
            MvPolynomial.map (Nat.castRingHom ℤ) (evG r) := by
        let φ₁ : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin m) ℤ :=
          (MvPolynomial.eval (fun j : Fin k => (g j : MvPolynomial (Fin m) ℤ))).comp splitMap
        let φ₂ : MvPolynomial (Fin (m + k)) ℕ →+* MvPolynomial (Fin m) ℤ :=
          (MvPolynomial.map (Nat.castRingHom ℤ)).comp evG
        have hhom : φ₁ = φ₂ := by
          apply MvPolynomial.ringHom_ext
          · intro c; simp [φ₁, φ₂, splitMap, evG]
          · intro idx
            simp only [φ₁, φ₂, RingHom.comp_apply, splitMap, evG, eval₂Hom_X']
            split_ifs with h1 <;> simp
        exact congrArg (fun f => f r) hhom
      rw [map_sub, hcomm p, hcomm q, hevG_eq, sub_self]
  -- Evaluate splitMap p = splitMap q in K!
  let v' : ℕ → K := fun i => if i < m + k then v i else 0
  have hv (i : ℕ) (hi : i < m + k) : v i = v' i := by simp [v', hi]
  rw [ringEval_congr_varsInRange (m + k) v v' hv e hve,
      ringEval_congr_varsInRange (m + k) v v' hv f hvf]
  let ψ : MvPolynomial (Fin k) (MvPolynomial (Fin m) ℤ) →+* K :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i : Fin m => v i.val))
      (fun j : Fin k => v (m + j.val))
  let φ : MvPolynomial (Fin (m + k)) ℕ →+* K := ψ.comp splitMap
  have hvar (i : ℕ) : φ (polyVar (m + k) i) = v' i := by
    dsimp only [φ, ψ, splitMap, polyVar, v']
    by_cases h1 : i < m + k
    · simp only [dif_pos h1, if_pos h1, RingHom.comp_apply, eval₂Hom_X']
      by_cases h2 : i < m
      · simp [h2]
      · simp only [dif_neg h2, eval₂Hom_X', Nat.add_sub_cancel' (Nat.le_of_not_lt h2)]
    · simp [h1]
  have h := congrArg ψ hsplit_eq
  change φ p = φ q at h
  simp only [p, q, map_add] at h
  have he' := splitEval_map φ (polyVar (m + k)) e
  have hf' := splitEval_map φ (polyVar (m + k)) f
  have heDiff := splitEval_difference (fun i => φ (polyVar (m + k) i)) e
  have hfDiff := splitEval_difference (fun i => φ (polyVar (m + k) i)) f
  rw [← he'] at heDiff; rw [← hf'] at hfDiff
  simp only [hvar] at heDiff hfDiff
  rw [← heDiff, ← hfDiff]
  linear_combination h

/-! Fast native `ℤ` / `ℕ` kernel evaluators (zero typeclass / `Finset.prod` overhead inside
`decide +kernel`!) and specialized `m = 2` Kronecker + `k`-grid theorem `identity_of_grid2`. -/


theorem identity_of_kronecker3With {K : Type*} [CommRing K]
    (v : ℕ → K) (d0 d1 d2 b : ℕ) (e f : Expr)
    (hchk : checkKronecker3With d0 d1 d2 b (Int.ofNat b) (Int.ofNat (Nat.pow b d0))
      (Int.ofNat (Nat.pow b (Nat.mul d0 d1))) e f = true) :
    ringEval v e = ringEval v f := by
  dsimp only [checkKronecker3With, fastMass3] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hve⟩, hvf⟩, hd0e⟩, hd1e⟩, hd2e⟩, hd0f⟩, hd1f⟩, hd2f⟩, hp⟩, hn⟩, hnum⟩
  let bound : Fin 3 → ℕ := ![d0, d1, d2]
  have hst0 : stride bound 0 = 1 := by simp [stride]
  have hst1 : stride bound 1 = d0 := by simp [stride, bound]
  have hst2 : stride bound 2 = d0 * d1 := by simp [stride, bound, Fin.prod_univ_three]
  let vB : ℕ → ℤ := fun
    | 0 => Int.ofNat b
    | 1 => Int.ofNat (Nat.pow b d0)
    | 2 => Int.ofNat (Nat.pow b (Nat.mul d0 d1))
    | _ => 0
  have hvB : vB = (fun i => (value bound b i : ℤ)) := by
    funext i; match i with
    | 0 => simp [vB, value, hst0]
    | 1 => simp [vB, value, hst1]
    | 2 => simp [vB, value, hst2]
    | i + 3 => simp [vB, value]
  apply identity_of_kronecker (n := 3) v bound b e f hb hve hvf
  · intro i; fin_cases i <;> simpa [bound]
  · intro i; fin_cases i <;> simpa [bound]
  · have hp' : _ < b := of_decide_eq_true hp
    simp only [fastSplitNat_eq] at hp'
    rw [positiveMass]
    convert hp' using 2; congr 1
    · congr 1; congr 1; funext i; match i with | 0 | 1 | 2 => rfl | i + 3 => simp
    · congr 1; congr 1; funext i; match i with | 0 | 1 | 2 => rfl | i + 3 => simp
  · have hn' : _ < b := of_decide_eq_true hn
    simp only [fastSplitNat_eq] at hn'
    rw [negativeMass]
    convert hn' using 2; congr 1
    · congr 1; congr 1; funext i; match i with | 0 | 1 | 2 => rfl | i + 3 => simp
    · congr 1; congr 1; funext i; match i with | 0 | 1 | 2 => rfl | i + 3 => simp
  · change fastEvalZ vB e = fastEvalZ vB f at hnum
    simpa only [fastEvalZ_eq, hvB] using hnum

theorem identity_of_kronecker3 {K : Type*} [CommRing K]
    (v : ℕ → K) (d0 d1 d2 b : ℕ) (e f : Expr)
    (hchk : checkKronecker3 d0 d1 d2 b e f = true) :
    ringEval v e = ringEval v f :=
  identity_of_kronecker3With v d0 d1 d2 b e f hchk


lemma biv_zero_of_checkBivZero3Aux {K : Type*} [CommRing K]
    (v : ℕ → K) (x y : K) (d0 d1 d2 b : ℕ) (r : Biv)
    (h : checkBivZero3Aux d0 d1 d2 b (Int.ofNat b) (Int.ofNat (Nat.pow b d0))
      (Int.ofNat (Nat.pow b (Nat.mul d0 d1))) r = true) :
    denote v x y r = 0 := by
  induction r with
  | nil => rfl
  | cons a i j p ih =>
    simp only [checkBivZero3Aux, Bool.and_eq_true] at h
    have ha : ringEval v a = 0 := by
      simpa [ringEval] using identity_of_kronecker3With v d0 d1 d2 b a (.num 0) h.1
    simp [denote, ha, ih h.2]

theorem biv_denote_eq_of_kronecker3 {K : Type*} [CommRing K]
    (v : ℕ → K) (x y : K) (d0 d1 d2 b : ℕ) (p q : Biv)
    (hchk : checkBivEq3 d0 d1 d2 b p q = true) :
    denote v x y p = denote v x y q := by
  have hz := biv_zero_of_checkBivZero3Aux v x y d0 d1 d2 b (merge 512 p (negBiv q)) hchk
  rw [merge_denote, negBiv_denote] at hz
  linear_combination hz


end PolynomialEncoding.KroneckerCheck

theorem solution
    {K : Type*} [CommRing K]
    (v : ℕ → K) (x y : K) (d0 d1 d2 b : ℕ)
    (p q : PolynomialEncoding.BivariateExpressions.Biv)
    (h : PolynomialEncoding.KroneckerCheck.checkBivEq3 d0 d1 d2 b p q = true) :
    PolynomialEncoding.BivariateExpressions.denote v x y p =
      PolynomialEncoding.BivariateExpressions.denote v x y q :=
  PolynomialEncoding.KroneckerCheck.biv_denote_eq_of_kronecker3 v x y d0 d1 d2 b p q h
