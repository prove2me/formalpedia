-- Prove2me | solution 1 for LX.CycleGeometry.pair_filled_gap_empty
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:35:17.653453+00:00
-- url     : https://prove2.me/submissions/10c8a86c-1b63-4b2f-945f-06cf07011c2b

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
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_PairCoreGeometry
import Definitions.Def_LX_PairCorePorts
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_Core_FiniteCuts_noncrossing_pair_contains_adjacent
import Theorems.Thm_LX_PairCore_permutation_noncrossing

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCoordinates
end LX.Core.FiniteCoordinates
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.PairCore
end LX.PairCore
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
/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}



















@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem mem_descendingPositions (p : State n) (i : Fin n) :
    i ∈ descendingPositions p ↔ (p i).val < i.val := by
  simp [descendingPositions]









@[simp] theorem descending_positions_one : descendingPositions (1 : State n) = ∅ := by
  ext i
  simp




















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



@[simp] theorem mem_fixedPositions (p : State n) (i : Fin n) :
    i ∈ fixedPositions p ↔ p i=i := by simp [fixedPositions]









end LX.Core.FiniteCuts

end

section
/-! Restrict a permutation and its lift to an invariant union of cycles.
Balance of the retained lift is stated separately from invariance. -/
namespace LX.Core.PrunedLift
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem permutation_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    permutation p S hS i=if i ∈ S then p i else i := rfl

@[simp] theorem permutation_symm_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    (permutation p S hS).symm i=if i ∈ S then p.symm i else i := rfl

end LX.Core.PrunedLift

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
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.PairCore
open scoped BigOperators
variable {n : ℕ}







@[simp] theorem permutation_apply (q : State n) (i : Fin n) :
    permutation q i=if q (q i)=i then q i else i := by
  simp [permutation,positions]

theorem permutation_involutive (q : State n) : Function.Involutive (permutation q) := by
  intro i
  by_cases hi : q (q i)=i
  · have hj := congrArg q hi
    simp only [permutation_apply,ite_eq_left hi,ite_eq_left hj]
    exact hi
  · simp only [permutation_apply,ite_eq_right hi]










end LX.PairCore

namespace LX.AnchoredPhases
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases

end

section
namespace LX.PairCore
variable {n : ℕ}



theorem pair_hits_ports (e : State n) (hinv : Function.Involutive e)
    (hnc : LX.Core.FiniteCuts.NoncrossingPairs e) (a b : Fin n)
    (hab : a.val < b.val) (he : e a=b) :
    ∃ x ∈ ports e,a.val ≤ x.val ∧ x.val ≤ b.val := by
  by_cases hf : ∃ x : Fin n,a.val ≤ x.val ∧ x.val ≤ b.val ∧ e x=x
  · obtain ⟨x,hax,hxb,hx⟩ := hf
    refine ⟨x,Finset.mem_union_left _ ((LX.Core.FiniteCuts.mem_fixedPositions e x).mpr hx),hax,hxb⟩
  · have hfixed (x : Fin n) (hax : a.val ≤ x.val) (hxb : x.val ≤ b.val) : e x ≠ x := by
      intro hx
      exact hf ⟨x,hax,hxb,hx⟩
    obtain ⟨x,y,hax,hyb,hxy,hex⟩ := LX.Core.FiniteCuts.noncrossing_pair_contains_adjacent
      e hinv hnc a b hab he hfixed
    refine ⟨x,Finset.mem_union_right _ ?_,hax,by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hex]; exact hxy⟩


end LX.PairCore

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]






end LX.AnchoredPhases

end

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- An invariant nonempty interval filled only by transpositions must
contain a fixed position or an adjacent pair. The latter is forbidden in
the majorized even source. -/
theorem solution (q : State n) (hq : cycleDefect q=0)
    (a c : Fin n)
    (hinv : ∀ b : Fin n,a.val < b.val → b.val < c.val →
      a.val < (q b).val ∧ (q b).val < c.val)
    (hpairs : ∀ b : Fin n,a.val < b.val → b.val < c.val → q (q b)=b)
    (hfixed : ∀ b : Fin n,a.val < b.val → b.val < c.val → q b ≠ b)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) : c.val ≤ a.val+1 := by
  by_contra hnot
  let b : Fin n := ⟨a.val+1,by have := c.isLt; omega⟩
  have hab : a.val < b.val := by dsimp [b]; omega
  have hbc : b.val < c.val := by dsimp [b]; omega
  have hqb := hinv b hab hbc
  have hneq := hfixed b hab hbc
  have hpair := hpairs b hab hbc
  let e := LX.PairCore.permutation q
  have he (i : Fin n) (hai : a.val < i.val) (hic : i.val < c.val) : e i=q i := by
    simp only [e,LX.PairCore.permutation_apply,ite_eq_left (hpairs i hai hic)]
  have hlt : b.val < (q b).val := by
    have hnv : (q b).val ≠ b.val := fun h => hneq (Fin.ext h)
    dsimp [b] at *
    omega
  obtain ⟨x,hx,hbx,hxq⟩ := LX.PairCore.pair_hits_ports e
    (LX.PairCore.permutation_involutive q) (LX.PairCore.permutation_noncrossing q hq)
    b (q b) hlt (he b hab hbc)
  have hax : a.val < x.val := by omega
  have hxc : x.val < c.val := by omega
  rcases Finset.mem_union.mp hx with hfix | hadj
  · have hx' := (mem_fixedPositions e x).mp hfix
    rw [he x hax hxc] at hx'
    exact hfixed x hax hxc hx'
  · have hx' := (Finset.mem_filter.mp hadj).2
    rw [he x hax hxc] at hx'
    exact hback x (q x) hx' (hpairs x hax hxc)
