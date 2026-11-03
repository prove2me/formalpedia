-- Prove2me | solution 1 for LX.Core.LiftedModel.x_changes_only_event
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:32:34.972232+00:00
-- url     : https://prove2.me/submissions/02d9b732-54b8-4865-8b07-dc2ce5f35685

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_LiftedModel_step_aligned

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace List
end List

section
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u

theorem ite_eq_left {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h

theorem ite_eq_right {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := if_neg h

end LX

namespace List
universe u

end List

/-
The following proof is adapted from Mathlib, copyright (c) 2026 Seewoo Lee,
licensed under Apache 2.0. Source revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Order/Floor/BigOperators.lean, lines 28-45.
-/
namespace Int
open scoped BigOperators


end Int

end

section
/-!
The L/R/X Cayley graph on `Equiv.Perm (Fin n)`. Right multiplication acts
on positions: `L` rotates the list to the left, `R` to the right, and `X`
exchanges its first two entries. The extended diameter avoids the convention
that a disconnected graph has natural-valued diameter zero.
-/
namespace LX.Core



















@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_cons {n : ℕ} [NeZero n] (a : Letter) (w : List Letter) :
    eval (n := n) (a :: w) = a.eval * eval w := by simp [eval]

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by simp [eval]






end LX.Core

end

section
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h




















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

end

section
/-! Physical positions, a paid cursor, and literal L/R/X words.
Every physical operation is proved to induce the same visible generator.
A realized balanced lift ends at the original target in its exact orientation. -/
namespace LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift



variable {n : ℕ} [NeZero n]















@[simp] theorem visible_initial : visible (initial (n := n)) = 1 := by
  simp [visible, initial]


end LX.Core.PhysicalModel

end

section
/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]







theorem neighboring_positions_distinct (hn : 2 ≤ n) (c : Fin n) : c ≠ c + 1 := by
  have h1 : (1 : Fin n) ≠ 0 := by
    intro h
    have := Fin.one_eq_zero_iff.mp h
    omega
  intro h
  have h' : c + 0 = c + 1 := by simpa using h
  exact h1 (add_left_cancel h').symm





























end LX.Core.LiftedModel

end

section
/-! Relative order of periodic token copies. A physical X changes the order of
exactly its own lifted pair orbit. This links reduced traces to inversions. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem positions_ne_periodic {s : Configuration n} (hs : Aligned s)
    (a b : Fin n) (hab : a ≠ b) (shift : ℤ) (hdiv : (n : ℤ) ∣ shift) :
    s.position a ≠ s.position b+shift := by
  intro he
  have hz : (shift : Fin n)=0 := by
    have h := AffineLift.cast_eq_of_modEq (Int.modEq_zero_iff_dvd.mpr hdiv)
    simpa using h
  have hc : (s.position a : Fin n)=(s.position b : Fin n) := by
    rw [he, Int.cast_add, hz, add_zero]
  rw [hs.2 a, hs.2 b] at hc
  exact hab (s.physical.tokens.symm.injective hc)











end LX.Core.LiftedModel

end

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (hn : 2 ≤ n) {s : Configuration n} (hs : Aligned s)
    (key : PairKey n) (hk : key.Valid) (hne : eventKey s ≠ key) :
    key.Before (step .x s) ↔ key.Before s := by
  have hab : key.first ≠ key.second := ne_of_lt hk.1
  have hpre := positions_ne_periodic hs key.first key.second hab key.shift hk.2
  have hpost := positions_ne_periodic (step_aligned hn .x hs)
    key.first key.second hab key.shift hk.2
  let a := s.physical.tokens s.physical.cursor
  let b := s.physical.tokens (s.physical.cursor+1)
  have hdist : a ≠ b := fun h => neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  by_contra hchange
  have horient :
      (key.first=a ∧ key.second=b ∧ key.shift=s.position a+1-s.position b) ∨
      (key.first=b ∧ key.second=a ∧ key.shift=-(s.position a+1-s.position b)) := by
    change ¬ ((s.position key.first+(if key.first=a then 1 else 0)-
      (if key.first=b then 1 else 0) <
      s.position key.second+(if key.second=a then 1 else 0)-
      (if key.second=b then 1 else 0)+key.shift) ↔
      s.position key.first < s.position key.second+key.shift) at hchange
    change s.position key.first+(if key.first=a then 1 else 0)-
      (if key.first=b then 1 else 0) ≠
      s.position key.second+(if key.second=a then 1 else 0)-
      (if key.second=b then 1 else 0)+key.shift at hpost
    by_cases hfa : key.first=a <;> by_cases hfb : key.first=b <;>
      by_cases hsa : key.second=a <;> by_cases hsb : key.second=b <;>
      simp_all <;> omega
  apply hne
  rcases horient with ⟨hfa, hsb, hz⟩ | ⟨hfb, hsa, hz⟩
  · have hnorm : normalizePair key.first key.second key.shift=key := by
      cases key
      simp only [normalizePair, ite_eq_left (le_of_lt hk.1)]
    simpa only [eventKey, a, b, hfa, hsb, hz] using hnorm
  · have hnorm : normalizePair key.second key.first (-key.shift)=key := by
      cases key
      simp only [normalizePair, ite_eq_right (not_le.mpr hk.1), neg_neg]
    simpa only [eventKey, a, b, hfb, hsa, hz, neg_neg] using hnorm
