-- Prove2me | solution 1 for LX.CycleGeometry.single_three_consecutive_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:44:25.872449+00:00
-- url     : https://prove2.me/submissions/8bd79ad7-c3dc-4c25-ba76-7e5045b428d2

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
import Definitions.Def_LX_PairCoreGeometry
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_CycleGeometry_excess_one_single_three
import Theorems.Thm_LX_CycleGeometry_outside_single_cycle_involutive
import Theorems.Thm_LX_CycleGeometry_single_cycle_support_interval_at_zero

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
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.PairCore
end LX.PairCore
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












end LX.PairCore

namespace LX.AnchoredPhases
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases

end

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A three-element interval support consists of three consecutive physical
positions. The forbidden backward unit arrow fixes the orientation. -/
theorem solution (q : State n) (hq : cycleDefect q=0)
    (he : q.support.card=2*q.cycleFactorsFinset.card+1)
    (hfixed : ∀ i : Fin n,q i=i → i=0)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) :
    ∃ a b c : Fin n,a.val+1=b.val ∧ b.val+1=c.val ∧
      q a=b ∧ q b=c ∧ q c=a ∧
      ∀ i : Fin n,i ≠ a → i ≠ b → i ≠ c → q (q i)=i := by
  classical
  obtain ⟨g,hg,hg3,hother⟩ := excess_one_single_three q he
  have hint := single_cycle_support_interval_at_zero q g hq hg hother hfixed hback
  have hnon : g.support.Nonempty := Finset.card_pos.mp (by omega)
  let a := g.support.min' hnon
  let c := g.support.max' hnon
  have ha : a ∈ g.support := Finset.min'_mem _ _
  have hc : c ∈ g.support := Finset.max'_mem _ _
  have hamin (i : Fin n) (hi : i ∈ g.support) : a.val ≤ i.val := Finset.min'_le _ _ hi
  have hcmax (i : Fin n) (hi : i ∈ g.support) : i.val ≤ c.val := Finset.le_max' _ _ hi
  have heq : g.support=Finset.Icc a c := by
    ext i
    simp only [Finset.mem_Icc,Fin.le_def]
    constructor
    · intro hi
      exact ⟨hamin i hi,hcmax i hi⟩
    · rintro ⟨hai,hic⟩
      by_cases hia : i=a
      · exact hia ▸ ha
      by_cases hic' : i=c
      · exact hic' ▸ hc
      exact hint a ha c hc i (by have : i.val ≠ a.val := fun h => hia (Fin.ext h); omega)
        (by have : i.val ≠ c.val := fun h => hic' (Fin.ext h); omega)
  have hac : a.val+2=c.val := by
    rw [heq,Fin.card_Icc] at hg3
    omega
  let b : Fin n := ⟨a.val+1,by have := c.isLt; omega⟩
  have hab : a.val+1=b.val := rfl
  have hbc : b.val+1=c.val := by dsimp [b]; omega
  have hb : b ∈ g.support := hint a ha c hc b (by omega) (by omega)
  have hmembers (i : Fin n) : i ∈ g.support ↔ i=a ∨ i=b ∨ i=c := by
    rw [heq,Finset.mem_Icc]
    change (a.val ≤ i.val ∧ i.val ≤ c.val) ↔ _
    constructor
    · intro hi
      have hv : i.val=a.val ∨ i.val=b.val ∨ i.val=c.val := by omega
      rcases hv with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    · rintro (rfl | rfl | rfl) <;> omega
  have hagree (i : Fin n) (hi : i ∈ g.support) : g i=q i := by
    rw [Equiv.Perm.cycle_is_cycleOf hi hg,Equiv.Perm.cycleOf_apply_self]
  have hmove (i : Fin n) (hi : i ∈ g.support) : q i ≠ i := by
    rw [← hagree i hi]
    exact Equiv.Perm.mem_support.mp hi
  have himage (i : Fin n) (hi : i ∈ g.support) : q i=a ∨ q i=b ∨ q i=c := by
    apply (hmembers _).mp
    rw [← hagree i hi]
    exact Equiv.Perm.apply_mem_support.mpr hi
  have hqb : q b=c := by
    rcases himage b hb with h | h | h
    · exact False.elim (hback a b hab h)
    · exact False.elim (hmove b hb h)
    · exact h
  have hqa : q a=b := by
    rcases himage a ha with h | h | h
    · exact False.elim (hmove a ha h)
    · exact h
    · have hab' := q.injective (h.trans hqb.symm)
      have hv := congrArg Fin.val hab'
      omega
  have hqc : q c=a := by
    rcases himage c hc with h | h | h
    · exact h
    · have hca := q.injective (h.trans hqa.symm)
      have hv := congrArg Fin.val hca
      omega
    · exact False.elim (hmove c hc h)
  refine ⟨a,b,c,hab,hbc,hqa,hqb,hqc,?_⟩
  intro i hia hib hic
  exact outside_single_cycle_involutive q g hg hother i (by
    rw [hmembers]
    tauto)
