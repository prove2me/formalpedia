-- Prove2me | solution 1 for MatchingLogic.two_copies_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:32.390066+00:00
-- url     : https://prove2.me/submissions/b9b0487d-8a89-4808-825a-b54b1fc003cd

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Theorems.Thm_MatchingLogic_two_copies

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
variable (M : Model S) (C : Set M.carrier)
namespace MatchingLogic
theorem _root_.solution (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    (ψ : Pattern S Var) (ν : Var → (C × Bool)) :
    (cover M C hne).denote ν ψ =
      {p : C × Bool | p.2 = false ∧
        (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star false (ν x)) ψ} ∪
      {p : C × Bool | p.2 = true ∧
        (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star true (ν x)) ψ} := by
  apply Set.ext
  intro p
  change p ∈ (cover M C hne).denote ν ψ ↔
    (p.2 = false ∧
      (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star false (ν x)) ψ) ∨
    (p.2 = true ∧
      (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star true (ν x)) ψ)
  rcases p with ⟨q, b⟩
  cases b with
  | false =>
      constructor
      · intro hp
        exact Or.inl ⟨rfl,
          (two_copies M C hC hne star hstar ψ ν (q, false)).mp hp⟩
      · rintro (⟨_, hp⟩ | ⟨hbad, _⟩)
        · exact (two_copies M C hC hne star hstar ψ ν (q, false)).mpr hp
        · cases hbad
  | true =>
      constructor
      · intro hp
        exact Or.inr ⟨rfl,
          (two_copies M C hC hne star hstar ψ ν (q, true)).mp hp⟩
      · rintro (⟨hbad, _⟩ | ⟨_, hp⟩)
        · cases hbad
        · exact (two_copies M C hC hne star hstar ψ ν (q, true)).mpr hp
end MatchingLogic
