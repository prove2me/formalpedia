-- Prove2me | solution 1 for MoserSchneckenreither.constructor_potential_estimate
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T05:08:00.640315+00:00
-- url     : https://prove2.me/submissions/5644dd3a-64cc-4ea5-a761-d554da3b8bbe

import Definitions.Def_MoserSchneckenreither_Typing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.NNRat

namespace MSThm7
open MoserSchneckenreither

variable {sig : Signature} {P : Problem sig}

theorem mem_symbols_arg {f : Symbol sig} {ts : Fin (sig.arity f) → Term sig}
    (i : Fin (sig.arity f)) {g : Symbol sig} (hg : g ∈ (ts i).symbols) :
    g ∈ (Term.app f ts).symbols := by
  simp only [Term.symbols]
  exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, hg⟩)

theorem raw_app (F : AnnotatedSignature P) (f : Symbol sig)
    (ts : Fin (sig.arity f) → Term sig) (q : Annotation) :
    rawPotential F (.app f ts) q =
      F.cost f q + ∑ i, rawPotential F (ts i) (F.input f q i) := by
  rw [rawPotential, List.sum_ofFn]

theorem raw_add (F : AnnotatedSignature P) (t : Term sig)
    (hs : ∀ f ∈ t.symbols, ConstructorLike P f) (p₁ p₂ : Annotation) :
    rawPotential F t (p₁ + p₂) = rawPotential F t p₁ + rawPotential F t p₂ := by
  induction t generalizing p₁ p₂ with
  | var x => simp [rawPotential]
  | app f ts ih =>
    have hf : ConstructorLike P f := hs f (by simp [Term.symbols])
    rw [raw_app, raw_app, raw_app, F.cost_add f hf]
    simp only [F.input_add f hf]
    have hA : ∀ i, rawPotential F (ts i) (F.input f p₁ i + F.input f p₂ i) =
        rawPotential F (ts i) (F.input f p₁ i) + rawPotential F (ts i) (F.input f p₂ i) :=
      fun i ↦ ih i (fun g hg ↦ hs g (mem_symbols_arg i hg)) _ _
    simp only [hA, Finset.sum_add_distrib]
    ring

theorem raw_mono (F : AnnotatedSignature P) (t : Term sig)
    (hs : ∀ f ∈ t.symbols, ConstructorLike P f) {p q : Annotation} (h : p ≤ q) :
    rawPotential F t p ≤ rawPotential F t q := by
  rw [← add_tsub_cancel_of_le h, raw_add F t hs]
  exact le_self_add

theorem raw_zero (F : AnnotatedSignature P) (t : Term sig)
    (hs : ∀ f ∈ t.symbols, ConstructorLike P f) : rawPotential F t 0 = 0 := by
  have h := raw_add F t hs 0 0
  rw [add_zero] at h
  simpa using h

theorem constr_symbols {t : Term sig} (h : t.Constructor) :
    ∀ f ∈ t.symbols, f ∈ sig.constructors := by
  induction h with
  | var x => simp [Term.symbols]
  | app c ts hc ht ih =>
    intro g hg
    simp only [Term.symbols, List.mem_cons, List.mem_flatten, List.mem_ofFn] at hg
    rcases hg with rfl | ⟨l, ⟨i, rfl⟩, hl⟩
    · exact hc
    · exact ih i g hl

theorem size_app (f : Symbol sig) (ts : Fin (sig.arity f) → Term sig) :
    (Term.app f ts).size = 1 + ∑ i, (ts i).size := by
  rw [Term.size, List.sum_ofFn]

theorem size_pos (t : Term sig) : 1 ≤ t.size := by
  cases t with
  | var x => simp [Term.size]
  | app f ts => rw [size_app]; omega

theorem degree_eq_zero {q : Annotation} (h : q.degree = 0) : q = 0 := by
  by_contra hne
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.2 hne
  have := Finset.le_sup (f := Nat.succ) ha
  unfold Annotation.degree at h
  omega

/-- The extra exponent term. -/
def ex (d s : ℕ) : ℕ := if 2 ≤ d then s ^ (d - 1) else 0

theorem sum_pow_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∑ i ∈ s, f i ^ m ≤ (∑ i ∈ s, f i) ^ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc f a ^ m + ∑ i ∈ s, f i ^ m ≤ f a ^ m + (∑ i ∈ s, f i) ^ m := by omega
      _ ≤ _ := pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) hm

theorem numeric {n : ℕ} (s : Fin n → ℕ) {d : ℕ} (hd : 1 ≤ d) :
    1 + ∑ i, (s i ^ d + ex d (s i)) ≤ (1 + ∑ i, s i) ^ d := by
  rw [Finset.sum_add_distrib]
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rcases k with _ | k
  · simp [ex]
  · have hex : ∀ x, ex (k + 1 + 1) x = x ^ (k + 1) := fun x ↦ by simp [ex]
    simp only [hex]
    have h1 := sum_pow_le Finset.univ s (m := k + 1 + 1) (by omega)
    have h2 := sum_pow_le Finset.univ s (m := k + 1) (by omega)
    generalize ∑ i, s i = S at *
    have h3 := pow_add_pow_le (Nat.zero_le 1) (Nat.zero_le S) (n := k + 1) (by omega)
    rw [one_pow] at h3
    have h4 : (1 + S ^ (k + 1)) * (1 + S) ≤ (1 + S) ^ (k + 1) * (1 + S) :=
      Nat.mul_le_mul_right _ h3
    have h5 : (1 + S ^ (k + 1)) * (1 + S) = 1 + S + S ^ (k + 1) + S ^ (k + 1 + 1) := by ring
    rw [pow_succ (1 + S) (k + 1)]
    omega

theorem main (F : AnnotatedSignature P) (hp : PolynomialConstructors F) :
    ∀ d, ∀ q : Annotation, q.degree ≤ d → ∀ v : Term sig, v.Constructor →
      rawPotential F v q ≤ q.maxCoeff * (v.size : ℚ≥0) ^ q.degree := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IHd =>
  intro q hq v hv
  induction hv with
  | var x => simp [rawPotential]
  | app c ts hc ht ih =>
    have hcl : ∀ i, ∀ f ∈ (ts i).symbols, ConstructorLike P f :=
      fun i f hf ↦ Or.inl (constr_symbols (ht i) f hf)
    have hcl' : ∀ f ∈ (Term.app c ts).symbols, ConstructorLike P f :=
      fun f hf ↦ Or.inl (constr_symbols (Term.Constructor.app c ts hc ht) f hf)
    by_cases hq0 : q = 0
    · subst hq0; rw [raw_zero F _ hcl']; exact zero_le
    obtain ⟨hcost, hin⟩ := hp c hc q hq0
    choose r hr1 hr2 hr3 using hin
    have hd1 : 1 ≤ q.degree := by
      by_contra h
      exact hq0 (degree_eq_zero (by omega))
    have hrb : ∀ i, rawPotential F (ts i) (r i) ≤
        q.maxCoeff * ((ex q.degree (ts i).size : ℕ) : ℚ≥0) := by
      intro i
      by_cases h2 : 2 ≤ q.degree
      · have hIH := IHd (r i).degree (lt_of_lt_of_le (hr3 i) hq) (r i) le_rfl (ts i) (ht i)
        have hs : (1 : ℚ≥0) ≤ ((ts i).size : ℚ≥0) := by exact_mod_cast size_pos (ts i)
        calc rawPotential F (ts i) (r i) ≤ (r i).maxCoeff * ((ts i).size : ℚ≥0) ^ (r i).degree :=
              hIH
          _ ≤ q.maxCoeff * ((ts i).size : ℚ≥0) ^ (q.degree - 1) :=
              mul_le_mul' (hr2 i) (pow_le_pow_right₀ hs (by have := hr3 i; omega))
          _ = _ := by simp [ex, h2]
      · have h0 : r i = 0 := degree_eq_zero (by have := hr3 i; omega)
        rw [h0, raw_zero F _ (hcl i)]
        exact zero_le
    have key : ∀ i, rawPotential F (ts i) (F.input c q i) ≤
        q.maxCoeff * ((ts i).size : ℚ≥0) ^ q.degree +
          q.maxCoeff * ((ex q.degree (ts i).size : ℕ) : ℚ≥0) := by
      intro i
      calc rawPotential F (ts i) (F.input c q i) ≤ rawPotential F (ts i) (q + r i) :=
            raw_mono F _ (hcl i) (hr1 i)
        _ = rawPotential F (ts i) q + rawPotential F (ts i) (r i) := raw_add F _ (hcl i) _ _
        _ ≤ _ := add_le_add (ih i) (hrb i)
    rw [raw_app, size_app]
    calc F.cost c q + ∑ i, rawPotential F (ts i) (F.input c q i)
        ≤ q.maxCoeff + ∑ i, (q.maxCoeff * ((ts i).size : ℚ≥0) ^ q.degree +
            q.maxCoeff * ((ex q.degree (ts i).size : ℕ) : ℚ≥0)) :=
          add_le_add hcost (Finset.sum_le_sum fun i _ ↦ key i)
      _ = q.maxCoeff * ((1 + ∑ i, ((ts i).size ^ q.degree + ex q.degree (ts i).size) : ℕ) :
            ℚ≥0) := by
          push_cast
          simp only [mul_add, Finset.mul_sum, mul_one]
      _ ≤ q.maxCoeff * (((1 + ∑ i, (ts i).size) ^ q.degree : ℕ) : ℚ≥0) :=
          by gcongr; exact numeric (fun i ↦ (ts i).size) hd1
      _ = _ := by push_cast; rfl

end MSThm7

open MoserSchneckenreither in
theorem solution {sig : Signature} {P : Problem sig}
    (F : AnnotatedSignature P) (hp : PolynomialConstructors F) (v : Term sig)
    (q : Annotation) (hg : v.Ground) (hv : v.Constructor) :
    potential F v q ≤ q.maxCoeff * (v.size : ℚ≥0) ^ q.degree := by
  classical
  have hsup : Supported P v := ⟨hg, fun f hf ↦ Or.inl (MSThm7.constr_symbols hv f hf)⟩
  unfold potential
  rw [if_pos hsup]
  exact MSThm7.main F hp q.degree q le_rfl v hv
