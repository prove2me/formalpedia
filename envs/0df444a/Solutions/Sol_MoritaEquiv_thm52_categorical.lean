-- Prove2me | solution 1 for MoritaEquiv.thm52_categorical
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-13T19:14:29.354029+00:00
-- url     : https://prove2.me/submissions/e7262d6f-a4ed-43c8-9fb7-bcb514393de1

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_ElemEmb_exists_of_sortwise_equiv
import Theorems.Thm_MoritaEquiv_nonempty_equivalence_discrete_of_classifier

open CategoryTheory

namespace MoritaEquiv
namespace T52C

/-! ### The theorem -/

open Thm52

theorem one_of {M : Str sig} (h : M.Satisfies exactlyOne) : ∀ x y : M.carrier (), x = y := by
  obtain ⟨c, hc⟩ : ∃ c : M.carrier (), ∀ y, y = c := by
    have := h (fun i => i.elim0)
    by_contra hne
    push Not at hne
    apply this
    intro c hc
    obtain ⟨y, hy⟩ := hne c
    exact hy (hc y)
  intro x y; rw [hc x, hc y]

/-- the set of predicates true at the (unique) element -/
def pset (M : Str sig) : Set ℕ := {i | ∀ x : M.carrier (), M.relMap (PRel.p i) (fun _ => x)}

theorem fun1 {M : Str sig} (xs : (j : Fin 1) → M.carrier (uctx 1 j)) : xs = fun _ => xs 0 := by
  funext j; rw [Subsingleton.elim j 0]

theorem pset_iff {M : Str sig} (h1 : ∀ x y : M.carrier (), x = y) (i : ℕ)
    (xs : (j : Fin 1) → M.carrier (uctx 1 j)) : M.relMap (PRel.p i) xs ↔ i ∈ pset M := by
  constructor
  · intro h x; rw [fun1 xs] at h; rwa [h1 x (xs 0)]
  · intro h; rw [fun1 xs]; exact h _

theorem sub_hom {M N : Str sig} (h1 : ∀ x y : N.carrier (), x = y) :
    Subsingleton (ElemEmb M N) := by
  constructor
  intro f g
  cases f; cases g
  congr
  funext s x
  exact h1 _ _

/-- the canonical one-point structure with predicate set `S` -/
def mk (S : Set ℕ) : Str sig where
  carrier _ := Unit
  funMap f _ := (f : Empty).elim
  relMap r _ := match r with | PRel.p i => i ∈ S
  nonempty _ := ⟨()⟩

theorem mk_sat (S : Set ℕ) : (mk S).Satisfies exactlyOne := by
  intro v h
  exact h () (fun y => rfl)

theorem mk_pset (S : Set ℕ) : pset (mk S) = S := by
  ext i; exact ⟨fun h => h (), fun h _ => h⟩

theorem hom_iff {M N : Str sig} (hM : ∀ x y : M.carrier (), x = y)
    (hN : ∀ x y : N.carrier (), x = y) : Nonempty (ElemEmb M N) ↔ pset M = pset N := by
  constructor
  · rintro ⟨f⟩
    ext i
    obtain ⟨x⟩ := M.nonempty ()
    have := f.map_formula (pAt i) (fun _ => x)
    rw [← pset_iff hM i, ← pset_iff hN i]
    exact this.symm
  · intro h
    obtain ⟨x⟩ := M.nonempty ()
    obtain ⟨y⟩ := N.nonempty ()
    let e : M.carrier () ≃ N.carrier () :=
      ⟨fun _ => y, fun _ => x, fun a => hM _ _, fun b => hN _ _⟩
    obtain ⟨g, -⟩ := ElemEmb.exists_of_sortwise_equiv (A := M) (B := N) (fun s => match s with | () => e)
      (fun f _ => (f : Empty).elim)
      (fun {m dom} r xs => by
        cases r with
        | p i => rw [pset_iff hM i, pset_iff hN i, h])
    exact ⟨g⟩

theorem T1_sat (M : Model T1) : M.str.Satisfies exactlyOne := M.isModel _ rfl
theorem T2_sat (M : Model T2) : M.str.Satisfies exactlyOne := M.isModel _ (Or.inl rfl)

/-- the valid predicate sets for `T₂` -/
def Good : Set (Set ℕ) := {S | 0 ∈ S → ∀ i, i ∈ S}

theorem T2_good (M : Model T2) : pset M.str ∈ Good := by
  intro h0 i
  have hM := one_of (T2_sat M)
  have := M.isModel _ (Or.inr ⟨i, rfl⟩) (fun _ => Classical.choice (M.str.nonempty ()))
  intro x
  have h := this ((pset_iff hM 0 _).2 h0)
  exact (pset_iff hM i _).1 h x

theorem mk_T2 (S : Set ℕ) (hS : S ∈ Good) : (mk S).IsModel T2 := by
  rintro A (hA | ⟨i, rfl⟩)
  · rw [hA]; exact mk_sat S
  · intro v h; exact hS h i

theorem equiv_good : Nonempty (Set ℕ ≃ Good) := by
  refine Function.Embedding.antisymm
    ⟨fun S => ⟨Nat.succ '' S, fun h => ?_⟩, fun S T h => ?_⟩
    ⟨Subtype.val, Subtype.val_injective⟩
  · obtain ⟨_, _, h⟩ := h; exact absurd h (Nat.succ_ne_zero _)
  · have := congrArg Subtype.val h
    exact Set.image_injective.2 Nat.succ_injective this

theorem t52_main : CategoricallyEquivalent T1 T2 := by
  obtain ⟨e1⟩ := nonempty_equivalence_discrete_of_classifier (C := Model T1) (fun M => pset M.str)
    (fun S => ⟨⟨mk S, by rintro A rfl; exact mk_sat S⟩, mk_pset S⟩)
    (fun X Y => sub_hom (one_of (T1_sat Y)))
    (fun X Y => hom_iff (one_of (T1_sat X)) (one_of (T1_sat Y)))
  obtain ⟨e2⟩ := nonempty_equivalence_discrete_of_classifier (C := Model T2) (fun M => (⟨pset M.str, T2_good M⟩ : Good))
    (fun S => ⟨⟨mk S.1, mk_T2 S.1 S.2⟩, Subtype.ext (mk_pset S.1)⟩)
    (fun X Y => sub_hom (one_of (T2_sat Y)))
    (fun X Y => (hom_iff (one_of (T2_sat X)) (one_of (T2_sat Y))).trans ⟨fun h => Subtype.ext h, congrArg Subtype.val⟩)
  obtain ⟨e⟩ := equiv_good
  exact ⟨e1.trans ((Discrete.equivalence e).trans e2.symm)⟩

end T52C
end MoritaEquiv

theorem solution : MoritaEquiv.CategoricallyEquivalent MoritaEquiv.Thm52.T1 MoritaEquiv.Thm52.T2 :=
  MoritaEquiv.T52C.t52_main
