-- Prove2me | solution 1 for Nary.eq_of_forall_dependency_getElem_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:53.163607+00:00
-- url     : https://prove2.me/submissions/e2564523-614c-427c-acff-86be681917ca

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary

set_option autoImplicit true
open Nary
namespace Nary
theorem _root_.solution {f : Func n α β} {I J : Vector α n} :
    (∀ (x : Dependency f), I[x.1] = J[x.1]) → f I = f J := by
  induction n with
  | zero =>
    intro h
    congr
    ext i hi
    contradiction
  | succ n ih =>
    intro h
    let g : Vector α n → β := fun v ↦ f (Vector.push v I[n])
    have h2 : ∀ V : Vector α (n + 1), I[n] = V[n] → f V = g V.pop := by
      intro V hV
      simp only [g]
      congr
      ext i hi
      rw [Vector.getElem_push]
      split
      next hh => simp only [Vector.getElem_pop']
      next hh =>
        have : i = n := by omega
        simp_all only [DependsOn, IndependentOf, Fin.getElem_fin, lt_self_iff_false, not_false_eq_true]
    by_cases hf : DependsOn f ⟨n, Nat.lt_add_one n⟩
    · have h1 := h ⟨⟨n, Nat.lt_add_one n⟩, hf⟩
      rw [h2 I rfl]
      rw [h2 J (by exact h1)]
      apply ih
      rintro ⟨x, hx⟩
      simp only [g] at hx
      have : DependsOn f x.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall] at hx
        rcases hx with ⟨a, V, hav⟩
        rw [show (V.set x a).push I[n] = (V.push I[n]).set x a by simp only [Vector.set_push, Fin.is_lt, ↓reduceDIte]] at hav
        simp only [DependsOn, IndependentOf, not_forall]
        use a, V.push I[n]
        exact hav
      have := h ⟨x.castSucc, this⟩
      simp_all only [DependsOn, IndependentOf, Fin.getElem_fin,
        Fin.val_castSucc, Vector.getElem_pop', g]
    · simp only [DependsOn, not_not, IndependentOf] at hf
      rw [hf I[n] J]
      rw [h2 I rfl]
      rw [h2 (J.set (⟨n, Nat.lt_add_one n⟩ : Fin (n + 1)) I[n]) (by simp only [Vector.getElem_set_self])]
      apply ih
      rintro ⟨x, hx⟩
      simp only [g] at hx
      have : DependsOn f x.castSucc := by
        simp only [DependsOn, IndependentOf, not_forall] at hx
        rcases hx with ⟨a, V, hav⟩
        rw [show (V.set x a).push I[n] = (V.push I[n]).set x a by simp [Vector.set_push]] at hav
        simp only [DependsOn, IndependentOf, not_forall]
        use a, V.push I[n]
        exact hav
      have := h ⟨x.castSucc, this⟩
      simp only [Fin.getElem_fin, Vector.getElem_pop']
      rw [Vector.getElem_set_ne _ _ (by omega)]
      simp_all only [DependsOn, IndependentOf, Fin.getElem_fin, Fin.val_castSucc]
end Nary
