-- Prove2me | solution 1 for MoritaEquiv.ElemEmb.exists_of_sortwise_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T19:14:31.260003+00:00
-- url     : https://prove2.me/submissions/93c3720d-5f05-440f-a884-ebe7618dfbed

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv
namespace T52C

universe u v w

variable {L : Sig}

theorem term_E {A B : Str L} (E : ∀ s, A.carrier s ≃ B.carrier s) {n : ℕ} {Γ : Fin n → L.Srt}
    (hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s) xs,
      E s (A.funMap f xs) = B.funMap f (fun j => E _ (xs j)))
    (v : (i : Fin n) → A.carrier (Γ i)) {s : L.Srt} (t : Term L Γ s) :
    t.realize B (fun i => E _ (v i)) = E s (t.realize A v) := by
  induction t with
  | var i => rfl
  | func f args ih =>
    show B.funMap f _ = E _ (A.funMap f _)
    rw [hf]
    congr 1
    funext j
    exact ih j

theorem cons_E {A B : Str L} (E : ∀ s, A.carrier s ≃ B.carrier s) {n : ℕ}
    {Γ' : Fin (n + 1) → L.Srt} (a : A.carrier (Γ' 0))
    (v : (i : Fin n) → A.carrier (Fin.tail Γ' i)) :
    (Fin.cons (α := fun i => B.carrier (Γ' i)) (E _ a) (fun i => E (Fin.tail Γ' i) (v i)) :
      (i : Fin (n + 1)) → B.carrier (Γ' i)) =
      fun i => E _ (Fin.cons (α := fun i => A.carrier (Γ' i)) a v i) := by
  funext i
  exact Fin.cases rfl (fun j => rfl) i

theorem emb_main {A B : Str L} (E : ∀ s, A.carrier s ≃ B.carrier s)
    (hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s) xs,
      E s (A.funMap f xs) = B.funMap f (fun j => E _ (xs j)))
    (hr : ∀ {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom) xs,
      B.relMap r (fun j => E _ (xs j)) ↔ A.relMap r xs) :
    ∃ h : ElemEmb A B, ∀ s x, h.toFun s x = E s x := by
  refine ⟨⟨fun s => E s, ?_⟩, fun _ _ => rfl⟩
  intro n Γ φ
  induction φ with
  | falsum => intro v; exact Iff.rfl
  | equal t₁ t₂ =>
    intro v
    show t₁.realize B _ = t₂.realize B _ ↔ t₁.realize A v = t₂.realize A v
    rw [term_E E hf v t₁, term_E E hf v t₂]
    exact (E _).injective.eq_iff
  | rel r args =>
    intro v
    show B.relMap r (fun j => (args j).realize B _) ↔ A.relMap r (fun j => (args j).realize A v)
    have : (fun j => (args j).realize B (fun i => E _ (v i))) =
        fun j => E _ ((args j).realize A v) := funext fun j => term_E E hf v (args j)
    rw [this]
    exact hr r _
  | imp φ ψ ihφ ihψ => intro v; exact imp_congr (ihφ v) (ihψ v)
  | all φ ih =>
    intro v
    constructor
    · intro h a
      have := h (E _ a)
      rw [cons_E E a v] at this
      exact (ih _).1 this
    · intro h b
      rw [← (E _).apply_symm_apply b, cons_E E _ v]
      exact (ih _).2 (h _)

end T52C
end MoritaEquiv

open MoritaEquiv in
theorem solution {L : Sig} {A B : Str L}
    (E : ∀ s, A.carrier s ≃ B.carrier s)
    (hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s)
      (xs : (j : Fin m) → A.carrier (dom j)),
      E s (A.funMap f xs) = B.funMap f (fun j => E _ (xs j)))
    (hr : ∀ {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom) (xs : (j : Fin m) → A.carrier (dom j)),
      B.relMap r (fun j => E _ (xs j)) ↔ A.relMap r xs) :
    ∃ h : ElemEmb A B, ∀ s x, h.toFun s x = E s x :=
  MoritaEquiv.T52C.emb_main E hf hr
