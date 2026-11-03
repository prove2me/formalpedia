-- Prove2me | solution 1 for LX.Core.RotationWords.twice_inversion_count
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:32:51.973171+00:00
-- url     : https://prove2.me/submissions/35e0959b-5c10-4e2a-9354-e077f4883291

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_AffineLift_crossing_antisymm

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
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
/-! The exact affine X price agrees with the crossing data derived from lifts. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem inversion_term_crossing (d : Fin n → ℤ) (i j : Fin n) (hij : i < j) :
    ((((j : ℤ)+d j)-((i : ℤ)+d i))/(n : ℤ)).natAbs=
      (AffineLift.crossing d i j).natAbs := by
  have hv : ((j-i : Fin n) : ℤ)=(j : ℤ)-(i : ℤ) := by
    rw [Fin.sub_val_of_le (le_of_lt hij), Nat.cast_sub (le_of_lt hij)]
  simp only [AffineLift.crossing, AffineLift.crossingNumerator, Int.natAbs_neg, hv]
  congr 2
  ring

omit [NeZero n] in
theorem inversion_count_crossings (d : Fin n → ℤ) :
    inversionCount (fun i : Fin n => (i : ℤ)+d i)=
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (AffineLift.crossing d i j).natAbs else 0 := by
  unfold inversionCount
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hij
  · exact inversion_term_crossing d i j hij
  · rfl


end LX.Core.LiftedModel

end

namespace LX.Core.RotationWords
end LX.Core.RotationWords
open LX
open LX.Core
open LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) :
    2*LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)=
      ∑ i : Fin n, ∑ j : Fin n, (AffineLift.crossing d i j).natAbs := by
  rw [LiftedModel.inversion_count_crossings, two_mul]
  have hp (i j : Fin n) :
      (if i < j then (AffineLift.crossing d i j).natAbs else 0)+
      (if j < i then (AffineLift.crossing d j i).natAbs else 0)=
      (AffineLift.crossing d i j).natAbs := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge (le_of_lt h)]
    · subst j; simp
    · rw [ite_eq_right (not_lt_of_ge (le_of_lt h)), ite_eq_left h, zero_add,
        AffineLift.crossing_antisymm hd i j, Int.natAbs_neg]
  calc
    _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then (AffineLift.crossing d i j).natAbs else 0)+
        ∑ i : Fin n, ∑ j : Fin n, if j < i then (AffineLift.crossing d j i).natAbs else 0 := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then (AffineLift.crossing d i j).natAbs else 0)+
        (if j < i then (AffineLift.crossing d j i).natAbs else 0)) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))
