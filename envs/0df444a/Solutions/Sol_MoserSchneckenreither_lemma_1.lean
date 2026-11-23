-- Prove2me | solution 1 for MoserSchneckenreither.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T03:03:31.597797+00:00
-- url     : https://prove2.me/submissions/0ced3bdf-2aef-4346-aafa-eafddb37d5fe

import Definitions.Def_MoserSchneckenreither_Annotations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.NNRat

namespace MSLemma1
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

theorem pot_add (F : AnnotatedSignature P) (v : Term sig) (p₁ p₂ : Annotation) :
    potential F v (p₁ + p₂) = potential F v p₁ + potential F v p₂ := by
  classical
  unfold potential
  by_cases h : Supported P v
  · simp only [if_pos h]; exact raw_add F v h.2 p₁ p₂
  · simp [if_neg h]

end MSLemma1

open MoserSchneckenreither in
theorem solution {sig : Signature} {P : Problem sig} (F : AnnotatedSignature P)
    (v : Term sig) (hv : v.Ground) (hn : Normal P.rules v) :
    (∀ p p₁ p₂ : Annotation, Shares p p₁ p₂ →
      potential F v p = potential F v p₁ + potential F v p₂) ∧
    (∀ p q : Annotation, p ≤ q → potential F v p ≤ potential F v q) := by
  refine ⟨fun p p₁ p₂ h ↦ ?_, fun p q h ↦ ?_⟩
  · rw [← h]; exact MSLemma1.pot_add F v p₁ p₂
  · rw [← add_tsub_cancel_of_le h, MSLemma1.pot_add]
    exact le_self_add
