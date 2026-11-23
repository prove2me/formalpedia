-- Prove2me | solution 1 for MoserSchneckenreither.footprint_identity_rootwise
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T02:32:31.305806+00:00
-- url     : https://prove2.me/submissions/816e92c2-1333-4f02-9772-a9a66e647420

import Definitions.Def_MoserSchneckenreither_Typing
import Definitions.Def_MoserSchneckenreither_RootPotential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace MSFootprint
open MoserSchneckenreither

variable {sig : Signature} {P : Problem sig}

theorem subst_subst (σ τ : ℕ → Term sig) (t : Term sig) :
    (t.subst τ).subst σ = t.subst (fun x ↦ (τ x).subst σ) := by
  induction t with
  | var x => rfl
  | app f ts ih => simp only [Term.subst, ih]

theorem symbols_subst_var (g : ℕ → ℕ) (t : Term sig) :
    (t.subst fun x ↦ .var (g x)).symbols = t.symbols := by
  induction t with
  | var x => rfl
  | app f ts ih => simp only [Term.subst, Term.symbols, ih]

theorem mem_symbols_arg {f : Symbol sig} {ts : Fin (sig.arity f) → Term sig} (i : Fin (sig.arity f))
    {g : Symbol sig} (hg : g ∈ (ts i).symbols) : g ∈ (Term.app f ts).symbols := by
  simp only [Term.symbols]
  exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, hg⟩)

theorem rootPotential_app (F : AnnotatedSignature P) {f : Symbol sig} (hf : ConstructorLike P f)
    (ts : Fin (sig.arity f) → Term sig) (q : Annotation) :
    rootPotential F (.app f ts) q =
      F.cost f q + ∑ i, rootPotential F (ts i) (F.input f q i) := by
  rw [rootPotential, if_pos hf, List.sum_ofFn]

theorem root_add (F : AnnotatedSignature P) (t : Term sig) (p₁ p₂ : Annotation) :
    rootPotential F t (p₁ + p₂) = rootPotential F t p₁ + rootPotential F t p₂ := by
  induction t generalizing p₁ p₂ with
  | var x => simp [rootPotential]
  | app f ts ih =>
    by_cases hf : ConstructorLike P f
    · rw [rootPotential_app F hf, rootPotential_app F hf, rootPotential_app F hf,
        F.cost_add f hf]
      simp only [F.input_add f hf, ih, Finset.sum_add_distrib]
      ring
    · simp [rootPotential, if_neg hf]

theorem ctx_append (F : AnnotatedSignature P) (σ : ℕ → Term sig) (Γ Δ : Context) :
    rootContextPotential F σ (Γ ++ Δ) = rootContextPotential F σ Γ + rootContextPotential F σ Δ := by
  simp [rootContextPotential]

theorem ctx_perm (F : AnnotatedSignature P) (σ : ℕ → Term sig) {Γ Δ : Context} (h : Γ.Perm Δ) :
    rootContextPotential F σ Γ = rootContextPotential F σ Δ :=
  (h.map _).sum_eq

theorem ctx_flat (F : AnnotatedSignature P) (σ : ℕ → Term sig) {n : ℕ} (xs : Fin n → ℕ)
    (ps : Fin n → Annotation) :
    rootContextPotential F σ (flatContext xs ps) = ∑ i, rootPotential F (σ (xs i)) (ps i) := by
  simp [rootContextPotential, flatContext, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem ctx_flatten (F : AnnotatedSignature P) (σ : ℕ → Term sig) (L : List Context) :
    rootContextPotential F σ L.flatten = (L.map (rootContextPotential F σ)).sum := by
  induction L with
  | nil => simp [rootContextPotential]
  | cons Γ L ih => rw [List.flatten_cons, ctx_append, ih, List.map_cons, List.sum_cons]

theorem ctx_flatten_ofFn (F : AnnotatedSignature P) (σ : ℕ → Term sig) {n : ℕ}
    (Γs : Fin n → Context) :
    rootContextPotential F σ (List.ofFn Γs).flatten = ∑ i, rootContextPotential F σ (Γs i) := by
  rw [ctx_flatten, List.map_ofFn, List.sum_ofFn]; rfl

theorem main (F : AnnotatedSignature P) {m : Mode} {Γ : Context} {k : ℚ≥0} {t : Term sig}
    {q : Annotation} (h : Typing F m Γ k t q) :
    m = .footprint → (∀ f ∈ t.symbols, ConstructorLike P f) → ∀ σ : ℕ → Term sig,
      rootPotential F (t.subst σ) q = rootContextPotential F σ Γ + k := by
  induction h with
  | app mode f a ha xs hx =>
    intro _ hs σ
    have hf : ConstructorLike P f := hs f (by simp [Term.symbols])
    obtain ⟨hin, hcost⟩ := F.constructor_unique f hf a ha
    simp only [Term.subst]
    rw [rootPotential_app F hf, ctx_flat, hin, hcost, add_comm]
  | var mode x q =>
    intro _ _ σ
    simp [Term.subst, rootContextPotential]
  | comp f ts xs ps Γs ks k₀ q hx hfresh hdisjoint hlinear hhead hargs ihhead ihargs =>
    intro hm hs σ
    classical
    let σ' : ℕ → Term sig := fun x ↦
      if h : ∃ i, xs i = x then (ts h.choose).subst σ else .var x
    have hσ' : ∀ i, σ' (xs i) = (ts i).subst σ := by
      intro i
      have h : ∃ j, xs j = xs i := ⟨i, rfl⟩
      simp only [σ', dif_pos h, hx h.choose_spec]
    have hf : ConstructorLike P f := hs f (by simp [Term.symbols])
    have hH := ihhead hm (by
      intro g hg
      simp only [Term.symbols, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hf
      · simp at hg) σ'
    have heq : (Term.app f fun i ↦ Term.var (xs i)).subst σ' = (Term.app f ts).subst σ := by
      simp only [Term.subst, hσ']
    rw [heq] at hH
    rw [hH, ctx_flat, ctx_flatten_ofFn]
    simp only [hσ']
    have hA : ∀ i, rootPotential F ((ts i).subst σ) (ps i) =
        rootContextPotential F σ (Γs i) + ks i :=
      fun i ↦ ihargs i hm (fun g hg ↦ hs g (mem_symbols_arg i hg)) σ
    simp only [hA, Finset.sum_add_distrib, List.sum_ofFn]
    ring
  | share Γ x y z p₁ p₂ p q t k hshare hxy hxz hyz hx hy hz h ih =>
    intro hm hs σ
    have hs' : ∀ f ∈ t.symbols, ConstructorLike P f := by
      intro f hf; apply hs; unfold Term.rename; rw [symbols_subst_var]; exact hf
    have hI := ih hm hs' (fun w ↦ σ (if w = x ∨ w = y then z else w))
    have hsub : (t.rename fun w ↦ if w = x ∨ w = y then z else w).subst σ =
        t.subst (fun w ↦ σ (if w = x ∨ w = y then z else w)) := by
      unfold Term.rename; rw [subst_subst]; rfl
    rw [hsub, hI, ctx_append, ctx_append]
    have hΓ : rootContextPotential F (fun w ↦ σ (if w = x ∨ w = y then z else w)) Γ =
        rootContextPotential F σ Γ := by
      unfold rootContextPotential
      congr 1
      apply List.map_congr_left
      intro a ha
      have hk : a.1 ∈ Γ.keys := List.mem_map.2 ⟨a, ha, rfl⟩
      have h1 : a.1 ≠ x := fun e ↦ hx (e ▸ hk)
      have h2 : a.1 ≠ y := fun e ↦ hy (e ▸ hk)
      simp [h1, h2]
    rw [hΓ]
    have hxy' : rootContextPotential F (fun w ↦ σ (if w = x ∨ w = y then z else w))
        [(x, p₁), (y, p₂)] = rootContextPotential F σ [(z, p)] := by
      simp only [rootContextPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        true_or, or_true, if_true, add_zero]
      rw [← root_add, hshare]
    rw [hxy']
  | perm hperm h ih =>
    intro hm hs σ
    rw [ih hm hs σ, ctx_perm F σ hperm]
  | w1 h hk ih => intro hm; cases hm
  | w2 Γ x p r q k t h hr ih => intro hm; cases hm
  | w3 h hq ih => intro hm; cases hm
  | w4 Γ x p q k t hx h ih => intro hm; cases hm

end MSFootprint

open MoserSchneckenreither in
theorem solution {sig : Signature} {P : Problem sig}
    (F : AnnotatedSignature P) {Γ : Context} {k : ℚ≥0} {t : Term sig} {q : Annotation}
    (h : Typing F .footprint Γ k t q) (hs : ∀ f ∈ t.symbols, ConstructorLike P f)
    (σ : ℕ → Term sig) :
    rootPotential F (t.subst σ) q = rootContextPotential F σ Γ + k :=
  MSFootprint.main F h rfl hs σ
