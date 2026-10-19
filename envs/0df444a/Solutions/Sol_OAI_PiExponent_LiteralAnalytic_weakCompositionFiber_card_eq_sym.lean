-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card_eq_sym
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T19:18:44.807934+00:00
-- url     : https://prove2.me/submissions/019075dc-c329-4702-aa2b-58e1ae81f7d6

import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_weakCompositionFiber

open scoped BigOperators

universe u

theorem solution
    (A : Type u) [Fintype A] [DecidableEq A] (k : Nat) :
    Fintype.card (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber A k) =
      Fintype.card (Sym A k) := by
  letI : Fintype {g : A → Nat // ∑ a, g a = k} :=
    Fintype.ofEquiv (Sym A k) (Sym.equivNatSumOfFintype A k)
  let e : OAI.PiExponent.LiteralAnalytic.weakCompositionFiber A k ≃
      {g : A → Nat // ∑ a, g a = k} :=
    { toFun := fun f => ⟨fun a => (f.1 a).val, by simpa using f.2⟩
      invFun := fun g => ⟨fun a => ⟨g.1 a, Nat.lt_succ_of_le (by
        calc
          g.1 a ≤ ∑ b : A, g.1 b :=
            Finset.single_le_sum (fun b hb => Nat.zero_le (g.1 b)) (Finset.mem_univ a)
          _ = k := g.2)⟩, by simpa using g.2⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext a
        apply Fin.ext
        rfl
      right_inv := by
        intro g
        apply Subtype.ext
        funext a
        rfl }
  calc
    Fintype.card (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber A k) =
        Fintype.card {g : A → Nat // ∑ a, g a = k} := Fintype.card_congr e
    _ = Fintype.card (Sym A k) :=
      Fintype.card_congr (Sym.equivNatSumOfFintype A k).symm