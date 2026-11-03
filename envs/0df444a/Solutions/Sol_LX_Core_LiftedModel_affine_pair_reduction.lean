-- Prove2me | solution 1 for LX.Core.LiftedModel.affine_pair_reduction
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:34:00.351212+00:00
-- url     : https://prove2.me/submissions/32b656f5-7f72-4037-9740-fab105092ebf

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
import Definitions.Def_LX_AffineDeletion
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_Core_LiftedModel_repeated_of_not_nodup
import Theorems.Thm_LX_Core_LiftedModel_x_as_pair_rename

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







theorem run_append (u v : List Letter) (s : Configuration n) :
    run (u ++ v) s = run v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => exact ih (step a s)





















end LX.Core.LiftedModel

end

section
/-! Periodic renaming of lifted tokens commutes with physical execution. The
integer offset is retained, so this symmetry records winding as well as labels. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem rename_step (q : State n) (offset : Fin n → ℤ) (a : Letter) (s : Configuration n) :
    rename q offset (step a s)=step a (rename q offset s) := by
  have he (i j : Fin n) : i=q.symm j ↔ q i=j := by
    constructor
    · intro h; rw [h, q.apply_symm_apply]
    · intro h; rw [← h, q.symm_apply_apply]
  cases a <;>
    simp [rename, step, increment, PhysicalModel.step, mul_assoc, Equiv.Perm.mul_apply,
      he, add_assoc, add_comm, add_left_comm, sub_eq_add_neg]

theorem rename_run (q : State n) (offset : Fin n → ℤ) (w : List Letter) (s : Configuration n) :
    rename q offset (run w s)=run w (rename q offset s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => rw [run, ih, rename_step, run]

omit [NeZero n] in
theorem rename_involutive (q : State n) (offset : Fin n → ℤ)
    (hq : Function.Involutive q) (hoffset : ∀ i, offset (q i)+offset i=0) :
    Function.Involutive (rename q offset) := by
  have hqi : q.symm=q := by
    apply Equiv.ext
    intro i
    apply q.injective
    rw [q.apply_symm_apply]
    exact (hq i).symm
  have hqq : q*q=1 := by
    apply Equiv.ext
    intro i
    exact hq i
  intro s
  have hp : (fun i => s.position (q (q i))+offset (q i)+offset i)=s.position := by
    funext i
    rw [hq, add_assoc, hoffset, add_zero]
  simp only [rename, hqi, ← mul_assoc, hqq, one_mul, hp]

/-- Two X events implementing the same involutive lifted renaming can both be
removed, while preserving the entire configuration and every integer position. -/
theorem delete_renamed_pair (q : State n) (offset : Fin n → ℤ)
    (hq : Function.Involutive q) (hoffset : ∀ i, offset (q i)+offset i=0)
    (middle : List Letter) (s : Configuration n)
    (hfirst : step .x s=rename q offset s)
    (hsecond : step .x (run middle (step .x s))=rename q offset (run middle (step .x s))) :
    run ([.x]++middle++[.x]) s=run middle s := by
  simp only [run_append, run]
  rw [hsecond, hfirst, ← rename_run]
  exact rename_involutive q offset hq hoffset (run middle s)



end LX.Core.LiftedModel

end

section
/-! A lifted pair is a pair of finite labels together with an integer relative
copy offset. Equal pair events implement the same periodic involution. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





omit [NeZero n] in
theorem pair_offset_cancel (a b : Fin n) (shift : ℤ) (hab : a ≠ b) (i : Fin n) :
    pairOffset a b shift (Equiv.swap a b i)+pairOffset a b shift i=0 := by
  by_cases ha : i=a
  · subst i; simp [pairOffset, Ne.symm hab]
  · by_cases hb : i=b
    · subst i; simp [pairOffset, Ne.symm hab]
    · simp [pairOffset, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]






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

omit [NeZero n] in
theorem normalize_pair_distinct (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    (normalizePair a b shift).first ≠ (normalizePair a b shift).second := by
  unfold normalizePair
  split_ifs <;> first | exact hab | exact Ne.symm hab

theorem event_pair_distinct (hn : 2 ≤ n) (s : Configuration n) :
    (eventKey s).first ≠ (eventKey s).second := by
  apply normalize_pair_distinct
  intro h
  exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)

theorem x_event_action (hn : 2 ≤ n) (s : Configuration n) :
    step .x s=(eventKey s).action s := by
  have hne : s.physical.tokens s.physical.cursor ≠ s.physical.tokens (s.physical.cursor+1) := by
    intro h
    exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  rw [eventKey, normalize_pair_action _ _ _ hne]
  exact x_as_pair_rename s _ _ hne rfl rfl



/-- Two equal canonical keys can be deleted even with an arbitrary middle word;
integer token positions, finite permutation and integer cursor all agree. -/
theorem delete_equal_events (hn : 2 ≤ n) (middle : List Letter) (s : Configuration n)
    (he : eventKey s=eventKey (run middle (step .x s))) :
    run ([.x]++middle++[.x]) s=run middle s := by
  let key := eventKey s
  have hne : key.first ≠ key.second := event_pair_distinct hn s
  apply delete_renamed_pair (Equiv.swap key.first key.second)
    (pairOffset key.first key.second key.shift)
    (Equiv.swap_apply_self _ _) (pair_offset_cancel _ _ _ hne)
  · exact x_event_action hn s
  · have h := x_event_action hn (run middle (step .x s))
    rw [← he] at h
    exact h

theorem delete_equal_events_context (hn : 2 ≤ n) (u middle v : List Letter)
    (s : Configuration n)
    (he : eventKey (run u s)=eventKey (run middle (step .x (run u s)))) :
    run (u++[.x]++middle++[.x]++v) s=run (u++middle++v) s := by
  have h := delete_equal_events hn middle (run u s) he
  simpa only [run_append, run] using congrArg (run v) h



end LX.Core.LiftedModel

end

section
/-! Repeated lifted pairs can be eliminated from every finite LX.Core word. The
integer endpoint configuration and the entire L/R subsequence are preserved.
Identifying the remaining number of X with affine inversion length is separate. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]



omit [NeZero n] in
theorem rotation_letters_delete (u middle v : List Letter) :
    rotationLetters (u++middle++v)=rotationLetters (u++[.x]++middle++[.x]++v) := by
  simp [rotationLetters, List.filter_append]











end LX.Core.LiftedModel

end

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

/-- Finite descent on literal word length removes every repeated lifted pair.
No permutation or winding information is lost, and no L/R letter is changed. -/
theorem solution (hn : 2 ≤ n) (w : List Letter) (s : Configuration n) :
    ∃ v : List Letter, run v s=run w s ∧ rotationLetters v=rotationLetters w ∧
      (events v s).Nodup ∧ v.length ≤ w.length ∧ v.Sublist w := by
  have aux : ∀ k : ℕ, ∀ w : List Letter, w.length=k → ∀ s : Configuration n,
      ∃ v : List Letter, run v s=run w s ∧ rotationLetters v=rotationLetters w ∧
        (events v s).Nodup ∧ v.length ≤ w.length ∧ v.Sublist w := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro w hw s
      by_cases hnd : (events w s).Nodup
      · exact ⟨w, rfl, rfl, hnd, le_rfl, List.Sublist.refl _⟩
      · obtain ⟨u, middle, tail, he, hk⟩ := repeated_of_not_nodup w s hnd
        let shorter := u++middle++tail
        have hlt : shorter.length < k := by
          dsimp [shorter]
          rw [he] at hw
          simp only [List.length_append, List.length_singleton] at hw ⊢
          omega
        have hend : run shorter s=run w s := by
          rw [he]
          exact (delete_equal_events_context hn u middle tail s hk).symm
        have hrot : rotationLetters shorter=rotationLetters w := by
          rw [he]
          exact rotation_letters_delete u middle tail
        have hdrop : shorter.Sublist w := by
          rw [he]
          have hh := ((List.sublist_append_left u [.x]).append
            (List.sublist_append_left middle [.x])).append (List.Sublist.refl tail)
          simpa only [shorter, List.append_assoc] using hh
        obtain ⟨v, hv, hr, hndv, hlen, hsub⟩ := ih shorter.length hlt shorter rfl s
        refine ⟨v, hv.trans hend, hr.trans hrot, hndv, ?_, hsub.trans hdrop⟩
        omega
  exact aux w.length w rfl s
