-- Prove2me | solution 1 for LX.LiftedScan.delete_event_word
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:33:43.243814+00:00
-- url     : https://prove2.me/submissions/40e26277-86cd-4bf6-89e1-380b2be1c3e8

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
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_LiftedScanBridge
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_LiftedModel_x_as_pair_rename
import Theorems.Thm_LX_Core_PhysicalModel_visible_step
import Theorems.Thm_LX_LiftedScan_mem_events

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











theorem visible_run (w : List Letter) (s : Configuration n) :
    visible (run w s) = visible s * eval w := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => rw [run, ih, visible_step, eval_cons, mul_assoc]



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









theorem run_physical (w : List Letter) (s : Configuration n) :
    (run w s).physical = PhysicalModel.run w s.physical := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih (step a s)



















end LX.Core.LiftedModel

end

section
/-! A lifted pair is a pair of finite labels together with an integer relative
copy offset. Equal pair events implement the same periodic involution. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]












omit [NeZero n] in
theorem pair_rename_reverse (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    pairRename b a (-shift)=pairRename a b shift := by
  have ho : pairOffset b a (-shift)=pairOffset a b shift := by
    funext i
    by_cases ha : i=a
    · subst i; simp [pairOffset, hab]
    · by_cases hb : i=b
      · subst i; simp [pairOffset, Ne.symm hab]
      · simp [pairOffset, ha, hb]
  simp only [pairRename, Equiv.swap_comm b a, ho]





end LX.Core.LiftedModel

end

section
/-! Canonical keys of lifted pair events. The stored shift is n times the copy
index, avoiding any loss through integer division. Order reversal negates it. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]







omit [NeZero n] in
theorem normalize_pair_action (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    (normalizePair a b shift).action=pairRename a b shift := by
  unfold normalizePair
  split_ifs
  · rfl
  · exact pair_rename_reverse a b shift hab





theorem x_event_action (hn : 2 ≤ n) (s : Configuration n) :
    step .x s=(eventKey s).action s := by
  have hne : s.physical.tokens s.physical.cursor ≠ s.physical.tokens (s.physical.cursor+1) := by
    intro h
    exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  rw [eventKey, normalize_pair_action _ _ _ hne]
  exact x_as_pair_rename s _ _ hne rfl rfl









end LX.Core.LiftedModel

end

section
namespace LX.Core



@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]








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





























end LX

end

section
namespace LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem visible_step (s : LX.Core.LiftedModel.Configuration n) (a : Letter) :
    visible (LX.Core.LiftedModel.step a.toCore s)=visible s*eval [a] := by
  change LX.Core.PhysicalModel.visible (LX.Core.PhysicalModel.step a.toCore s.physical)=_
  rw [LX.Core.PhysicalModel.visible_step]
  congr 1









theorem visible_run (w : List Letter) (s : LX.Core.LiftedModel.Configuration n) :
    visible (LX.Core.LiftedModel.run (w.map Letter.toCore) s)=visible s*eval w := by
  unfold visible
  rw [LX.Core.LiftedModel.run_physical,LX.Core.PhysicalModel.visible_run]
  rfl

theorem visible_run_initial (w : List Letter) :
    visible (LX.Core.LiftedModel.run (w.map Letter.toCore) (LX.Core.LiftedModel.initial (n := n)))=eval w := by
  rw [visible_run]
  simp [visible,LX.Core.LiftedModel.initial]

/-- The event's finite transposition is the actual conjugate of X by the
current visible configuration. The periodic shift is retained in the event key. -/
theorem event_swap_visible (hn : 2 ≤ n) (s : LX.Core.LiftedModel.Configuration n) :
    Equiv.swap (LX.Core.LiftedModel.eventKey s).first (LX.Core.LiftedModel.eventKey s).second*visible s=
      visible s*eval [.x] := by
  have hh := congrArg (fun t : LX.Core.LiftedModel.Configuration n => visible t)
    (LX.Core.LiftedModel.x_event_action hn s)
  change visible (LX.Core.LiftedModel.step Letter.x.toCore s)=_ at hh
  rw [visible_step] at hh
  simpa only [visible,LX.Core.LiftedModel.PairKey.action,LX.Core.LiftedModel.pairRename,
    LX.Core.LiftedModel.rename,LX.Core.PhysicalModel.visible,Equiv.symm_swap,mul_assoc] using hh.symm













end LX.LiftedScan

end

namespace LX.LiftedScan
end LX.LiftedScan
open LX
open LX.LiftedScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Deleting an observed X sorts the input with those two original positions
transposed. Exactly one exchange is removed and all rotations are retained. -/
theorem solution (hn : 2 ≤ n) (p : State n) (w : List Letter)
    (hp : p*eval w=1) (key : LX.Core.LiftedModel.PairKey n)
    (hkey : key ∈ LX.Core.LiftedModel.events (w.map Letter.toCore) LX.Core.LiftedModel.initial) :
    ∃ v : List Letter,(p*Equiv.swap key.first key.second)*eval v=1 ∧
      v.length+1=w.length ∧ v.count .l=w.count .l := by
  obtain ⟨u,v,hw,hk⟩ := (mem_events w LX.Core.LiftedModel.initial key).mp hkey
  have hs := event_swap_visible hn (LX.Core.LiftedModel.run (u.map Letter.toCore) LX.Core.LiftedModel.initial)
  rw [hk,visible_run_initial] at hs
  rw [hw,eval_append,eval_append] at hp
  refine ⟨u++v,?_,?_,?_⟩
  · rw [eval_append]
    calc
      _ = p*((Equiv.swap key.first key.second*eval u)*eval v) := by group
      _ = p*((eval u*eval [.x])*eval v) := by rw [hs]
      _ = 1 := hp
  · simp [hw]
    omega
  · simp [hw]
