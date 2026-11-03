-- Prove2me | solution 1 for LX.exists_shortest_greedy_word
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:11:29.019998+00:00
-- url     : https://prove2.me/submissions/43f4dd2b-dcf7-464f-b52b-e36d836ea251

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
import Definitions.Def_LX_Connected
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_exists_greedy_normal_form

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
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
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace List
end List

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

theorem Letter.eval_mem {n : ℕ} [NeZero n] (a : Letter) :
    a.eval (n := n) ∈ generators n := by
  cases a <;> simp [Letter.eval, generators]




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
namespace LX.Core



theorem connected_of_generates {G : Type*} [Group G] (S : Set G)
    (hgen : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  have hsub : Subgroup.closure S ≤ reachableSubgroup S := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change (SimpleGraph.mulCayley S).Reachable 1 g
    by_cases h : 1 = g
    · rw [← h]
    · exact ((SimpleGraph.mulCayley_adj' S 1 g).mpr
        ⟨h, g, hg, Or.inl (one_mul g)⟩).reachable
  rw [hgen] at hsub
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  exact ⟨1, fun g => hsub (Subgroup.mem_top g)⟩

theorem generators_closure (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    Subgroup.closure (generators n) = ⊤ := by
  have hrot : L n (0 : Fin n) = 1 := by
    cases n with
    | zero => omega
    | succ k => exact finRotate_apply_zero
  have hgen := Equiv.Perm.closure_cycle_adjacent_swap
    (isCycle_finRotate_of_le hn)
    (support_finRotate_of_le hn) (0 : Fin n)
  change Subgroup.closure ({L n, Equiv.swap 0 (L n 0)} : Set (State n)) = ⊤ at hgen
  rw [hrot] at hgen
  apply top_unique
  rw [← hgen]
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> simp [generators, X]

theorem connected (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (graph n).Connected :=
  connected_of_generates _ (generators_closure n hn)


end LX.Core

end

section
/-! A zero-displacement phase lift is an actual rotation. Its final rotation
is explicitly paid by an LX.Core word of length at most n-1. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_power_apply (k : ℕ) (i : Fin n) : (L n ^ k) i = i + (k : Fin n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [L, finRotate_apply, Nat.cast_add, add_comm, add_left_comm]


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
/-! The cyclic generator has period `n`.
This identity allows inverse rotations to be expanded into forward words. -/
namespace LX.Core.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_period : L n ^ n=1 := by
  apply Equiv.ext
  intro i
  simp [AffineLift.rotation_power_apply]


end LX.Core.RotationWords

end

section
namespace LX.Core



@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]

theorem generator_is_letter {n : ℕ} [NeZero n] {g : State n}
    (hg : g ∈ generators n) : ∃ c : Letter, c.eval = g := by
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨.l, rfl⟩
  · exact ⟨.r, rfl⟩
  · exact ⟨.x, rfl⟩

theorem adj_iff_letter {n : ℕ} [NeZero n] (a b : State n) :
    (graph n).Adj a b ↔ a ≠ b ∧ ∃ c : Letter, a * c.eval = b := by
  rw [graph, SimpleGraph.mulCayley_adj']
  constructor
  · rintro ⟨hne, g, hg, h⟩
    obtain ⟨c, rfl⟩ := generator_is_letter hg
    refine ⟨hne, ?_⟩
    rcases h with h | h
    · exact ⟨c, h⟩
    · refine ⟨c.inverse, ?_⟩
      rw [Letter.eval_inverse, h, mul_inv_cancel_right]
  · rintro ⟨hne, c, hc⟩
    exact ⟨hne, c.eval, c.eval_mem, Or.inl hc⟩

/-- Every graph walk has a literal L/R/X word of exactly the same length. -/
theorem word_of_walk {n : ℕ} [NeZero n] {a b : State n}
    (p : (graph n).Walk a b) :
    ∃ w : List Letter, a * eval w = b ∧ w.length = p.length := by
  induction p with
  | nil => exact ⟨[], by simp, rfl⟩
  | @cons a b d hab p ih =>
    obtain ⟨c, hc⟩ := ((adj_iff_letter a b).mp hab).2
    obtain ⟨w, hw, hlen⟩ := ih
    refine ⟨c :: w, ?_, by simp [hlen]⟩
    rw [eval_cons, ← mul_assoc, hc, hw]


end LX.Core

end

section
/-! Directed LX words. No inverse generator is included in the alphabet.
The target bound is a proposition, not an axiom or an assumed estimate. -/
namespace LX









@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by
  simp [eval]





theorem expandLetter_eval {n : ℕ} [NeZero n] (c : LX.Core.Letter) :
    eval (expandLetter n c) = c.eval (n := n) := by
  cases c with
  | l => simp [expandLetter, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval]
  | x => simp [expandLetter, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval]
  | r =>
    have hn : 0 < n := NeZero.pos n
    have hp := LX.Core.RotationWords.rotation_period (n := n)
    have he : LX.Core.L n ^ (n - 1) * LX.Core.L n = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hn, hp]
    have hi : LX.Core.L n ^ (n - 1) = (LX.Core.L n)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left he
    simpa [expandLetter, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval, LX.Core.R] using hi

theorem expand_eval {n : ℕ} [NeZero n] (w : List LX.Core.Letter) :
    eval (expand n w) = LX.Core.eval (n := n) w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change eval (expandLetter n c ++ expand n w) = _
    rw [eval_append, expandLetter_eval, ih, LX.Core.eval_cons]

theorem exists_word {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w = p := by
  obtain ⟨path⟩ := LX.Core.connected n hn 1 p
  obtain ⟨w, hw, _⟩ := LX.Core.word_of_walk path
  exact ⟨expand n w, by simpa [expand_eval] using hw⟩



theorem length_le_word {n : ℕ} [NeZero n] (w : List Letter) :
    length (eval (n := n) w) ≤ w.length := by
  exact Nat.sInf_le ⟨w, rfl, rfl⟩

theorem exists_shortest_word {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w = p ∧ w.length = length p := by
  obtain ⟨w, hw⟩ := exists_word hn p
  exact Nat.sInf_mem (show Set.Nonempty {k : ℕ | ∃ w : List Letter,
    eval w = p ∧ w.length = k} from ⟨w.length, w, hw, rfl⟩)













end LX

end

namespace LX
end LX
open LX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every directed distance is attained within the proved greedy normal
form family. No restriction to minimum energy or minimum height is made. -/
theorem solution (hn : 2 ≤ n) (p : State n) :
    ∃ c : ℕ,∃ d : Fin n → ℤ,∃ g : List Letter,
      IsLift p (c : ℤ) d ∧ ScanTrace d g ∧
      eval (paidWord (c : Fin n) g)=p ∧
      (paidWord (c : Fin n) g).length=length p := by
  obtain ⟨w,hw,hlen⟩ := exists_shortest_word hn p
  obtain ⟨d,g,hd,hg,he,hbound⟩ := exists_greedy_normal_form hn w
  rw [hw] at hd he
  refine ⟨w.count .l,?_⟩
  refine ⟨d,?_⟩
  refine ⟨g,?_⟩
  refine ⟨hd,?_⟩
  refine ⟨hg,?_⟩
  refine ⟨he,?_⟩
  have hlo := length_le_word (n := n) (paidWord (w.count .l : Fin n) g)
  rw [he] at hlo
  exact Nat.le_antisymm (hbound.trans_eq hlen) hlo
