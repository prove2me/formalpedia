-- Prove2me | solution 1 for LX.CycleGeometry.zero_defect_invariant_gap_fixed
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:45:14.515747+00:00
-- url     : https://prove2.me/submissions/fe72dd08-b446-41ae-a696-908c3df18d02

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_ShallowNeighborSplice
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventTravel
import Theorems.Thm_LX_Core_FiniteCuts_linear_sorting_events
import Theorems.Thm_LX_Core_FiniteCuts_zero_defect_pruned_factor
import Theorems.Thm_LX_Core_ZeroGap_minimal_interval_event_unit_arrow

namespace Int
end Int
namespace LX
end LX
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
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
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem displacement_mass_inverse (p : State n) :
    (∑ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p.symm i|)=∑ i : Fin n, |_root_.LX.Core.FiniteCuts.displacement p i| := by
  have h := Equiv.sum_comp p (fun i : Fin n => |_root_.LX.Core.FiniteCuts.displacement p.symm i|)
  simpa only [_root_.LX.Core.FiniteCuts.displacement,Equiv.symm_apply_apply,abs_sub_comm] using h.symm


end LX.Core.FiniteCuts

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

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open scoped BigOperators
open LX.Core.FiniteCuts LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- An invariant interval with no fixed point would have a unit arrow in
its minimal sorting-event forest. Thus forbidding unit arrows forces a
fixed point in every nonempty invariant interval. -/
theorem solution (q : State n) (hq : cycleDefect q=0)
    (hunit : ∀ i : Fin n,|_root_.LX.Core.FiniteCuts.displacement q i| ≠ 1)
    (a c b : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val)
    (hinv : ∀ i : Fin n,(a.val < (q i).val ∧ (q i).val < c.val) ↔
      (a.val < i.val ∧ i.val < c.val)) :
    ∃ i : Fin n,a.val < i.val ∧ i.val < c.val ∧ q i=i := by
  classical
  by_contra hnone
  let S := Finset.univ.filter (fun i : Fin n => a.val < i.val ∧ i.val < c.val)
  have hS (i : Fin n) : q i ∈ S ↔ i ∈ S := by
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hinv i
  let g := LX.Core.PrunedLift.permutation q S hS
  have hgzero : cycleDefect g=0 := zero_defect_pruned_factor q S hS hq
  have hgSupport : g.support=S := by
    ext i
    simp only [Equiv.Perm.mem_support]
    by_cases hi : i ∈ S
    · have hb' := (Finset.mem_filter.mp hi).2
      have hmove : q i ≠ i := fun he => hnone ⟨i,hb'.1,hb'.2,he⟩
      simp [g,hi,hmove]
    · simp [g,hi]
  obtain ⟨events,hprod,hlen,hactive,hlin,hsep,_⟩ := linear_sorting_events g
  have hcount : (g⁻¹).cycleFactorsFinset.card=g.cycleFactorsFinset.card := by
    have hh := congrArg Multiset.card (Equiv.Perm.cycleType_inv g)
    simpa [Equiv.Perm.cycleType] using hh
  have hminimal : events.length+(g⁻¹).cycleFactorsFinset.card=g.support.card := by
    rw [hcount]
    rw [displacement_mass_inverse] at hlen
    unfold cycleDefect at hgzero
    omega
  have hnon : g.support.Nonempty := by
    rw [hgSupport]
    exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab,hbc⟩⟩
  have hinter : CarrierInterval g.support Finset.univ := by
    rw [hgSupport]
    refine ⟨Finset.subset_univ _,?_⟩
    intro x hx y hy z _ hxz hzy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega,by omega⟩
  obtain ⟨i,hi⟩ := minimal_interval_event_unit_arrow events g hprod hactive hlin hsep hnon hinter hminimal
  have his : i ∈ S := by
    by_contra hiS
    have hgi : g i=i := by simp [g,hiS]
    simp only [_root_.LX.Core.FiniteCuts.displacement,hgi,sub_self,abs_zero] at hi
    omega
  have hgi : g i=q i := by simp [g,his]
  apply hunit i
  simpa only [_root_.LX.Core.FiniteCuts.displacement,hgi] using hi
