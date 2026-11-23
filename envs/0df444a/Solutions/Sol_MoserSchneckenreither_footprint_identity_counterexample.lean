-- Prove2me | solution 1 for MoserSchneckenreither.footprint_identity_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T03:03:32.218306+00:00
-- url     : https://prove2.me/submissions/0f5eea37-b65f-4da3-8b62-774fc98ac478

import Definitions.Def_MoserSchneckenreither_Typing

namespace MSFootCex
open MoserSchneckenreither

/-- Symbol 0 is a unary constructor `c`; symbol 1 is a defined constant `d`. -/
def ar : Fin 2 → ℕ
  | 0 => 1
  | 1 => 0

abbrev sig : Signature where
  count := 2
  arity := ar
  constructors := {0}
  constructors_nonempty := ⟨0, Finset.mem_singleton_self 0⟩
  has_constant := ⟨1, rfl⟩

def P : Problem sig := ⟨[], []⟩

theorem not_rewrites (t u : Term sig) : ¬ Rewrites P.rules t u := by
  intro h
  induction h with
  | root r hr _ => simp [P, Problem.rules] at hr
  | arg _ _ _ _ _ _ ih => exact ih

theorem constructorLike_iff (f : Symbol sig) : ConstructorLike P f ↔ f = 0 := by
  simp [ConstructorLike, P, Problem.rules, sig]

noncomputable def F : AnnotatedSignature P where
  declarations f a := a = ⟨fun _ ↦ a.output, a.output 0, a.output⟩
  nonempty f := ⟨⟨fun _ ↦ 0, (0 : Annotation) 0, 0⟩, rfl⟩
  input _ q _ := q
  cost _ q := q 0
  constructor_declaration _ _ _ := rfl
  constructor_unique _ _ _ h := ⟨congrArg Declaration.inputs h, congrArg Declaration.cost h⟩
  input_add _ _ _ _ _ := rfl
  cost_add _ _ p q := Finsupp.add_apply p q 0
  input_scale _ _ _ _ _ := rfl
  cost_scale _ _ a q := by simp [Annotation.scale]

abbrev c : Symbol sig := (0 : Fin 2)
abbrev d : Symbol sig := (1 : Fin 2)

def dTerm : Term sig := Term.app d (fun i ↦ Fin.elim0 i)

def σ : Substitution sig := ⟨{0}, fun _ ↦ dTerm⟩

def xs : Fin (sig.arity c) → ℕ := fun _ ↦ 0

theorem xs_inj : Function.Injective xs := by
  intro i j _
  exact Fin.ext (by have := i.2; have := j.2; simp [sig, ar, c] at *; omega)

noncomputable def q : Annotation := Finsupp.single 0 1

noncomputable def decl : Declaration (sig.arity c) := ⟨fun _ ↦ q, q 0, q⟩

def t : Term sig := Term.app c fun i ↦ Term.var (xs i)

theorem d_not_cl : ¬ ConstructorLike P d := by
  rw [constructorLike_iff]; decide

theorem pot_zero (u : Term sig) (hu : d ∈ u.symbols) (p : Annotation) : potential F u p = 0 := by
  rw [potential, if_neg]
  rintro ⟨_, h⟩
  exact d_not_cl (h d hu)

theorem mem_symbols_arg {f : Symbol sig} {ts : Fin (sig.arity f) → Term sig} (i : Fin (sig.arity f))
    {g : Symbol sig} (hg : g ∈ (ts i).symbols) : g ∈ (Term.app f ts).symbols := by
  simp only [Term.symbols]
  exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, hg⟩)

theorem hΓ : flatContext xs decl.inputs = [(0, q)] := rfl

theorem d_mem : d ∈ dTerm.symbols := List.mem_cons_self

theorem hsubst : t.subst σ.apply = Term.app c (fun _ ↦ dTerm) := by
  simp only [t, Term.subst]
  congr 1

theorem t_symbols : t.symbols = [c] := rfl

theorem main :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t : Term sig) (q : Annotation) (k : ℚ≥0),
      σ.Normalised P ∧ (∀ x ∈ Γ.keys, x ∈ σ.domain) ∧
      Typing F .footprint Γ k t q ∧ (∀ f ∈ t.symbols, ConstructorLike P f) ∧
      potential F (t.subst σ.apply) q ≠ contextPotential F σ Γ + k := by
  refine ⟨sig, P, F, flatContext xs decl.inputs, σ, t, q, decl.cost, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    refine ⟨?_, fun ⟨u, hu⟩ ↦ not_rewrites _ _ hu⟩
    show dTerm.vars = []
    rfl
  · intro x hx
    rw [hΓ] at hx
    simp [Context.keys] at hx
    simp [σ, hx]
  · exact Typing.app .footprint c decl rfl xs xs_inj
  · intro f hf
    rw [t_symbols, List.mem_singleton] at hf
    rw [constructorLike_iff, hf]
  · have h1 : potential F (t.subst σ.apply) q = 0 := by
      rw [hsubst]
      exact pot_zero _ (mem_symbols_arg (f := c) (ts := fun _ ↦ dTerm) ⟨0, by decide⟩ d_mem) _
    have h2 : contextPotential F σ (flatContext xs decl.inputs) = 0 := by
      rw [hΓ]
      simp only [contextPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      have : σ.apply 0 = dTerm := by simp [Substitution.apply, σ]
      rw [this]
      exact pot_zero _ d_mem _
    rw [h1, h2]
    simp [decl, q]

end MSFootCex

open MoserSchneckenreither in
theorem solution :
    ∃ (sig : Signature) (P : Problem sig) (F : AnnotatedSignature P) (Γ : Context)
      (σ : Substitution sig) (t : Term sig) (q : Annotation) (k : ℚ≥0),
      σ.Normalised P ∧ (∀ x ∈ Γ.keys, x ∈ σ.domain) ∧
      Typing F .footprint Γ k t q ∧ (∀ f ∈ t.symbols, ConstructorLike P f) ∧
      potential F (t.subst σ.apply) q ≠ contextPotential F σ Γ + k :=
  MSFootCex.main
