-- Prove2me | solution 1 for LX.Core.FiniteCuts.shifted_capacity_equality_support
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:58:26.711454+00:00
-- url     : https://prove2.me/submissions/f0c5cb19-534b-432e-a667-a925d2729cb2

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_StrictBandInversionCapacity
import Theorems.Thm_LX_Core_FiniteCuts_shifted_capacity_equality
import Theorems.Thm_LX_Core_FiniteCuts_shifted_support_add_extreme_count

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
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
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
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

theorem cycle_support_card_sum (p : State n) :
    ∑ q ∈ p.cycleFactorsFinset, q.support.card=p.support.card := by
  classical
  obtain ⟨l,hn,heq⟩ := p.cycleFactorsFinset.exists_list_nodup_eq
  have h := (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset hn).mp heq.symm
  have hc := Equiv.Perm.card_support_prod_list_of_pairwise_disjoint h.2.1
  rw [h.2.2] at hc
  rw [← heq, List.sum_toFinset _ hn]
  exact hc.symm

theorem twice_cycle_count_le_support (p : State n) :
    2*p.cycleFactorsFinset.card ≤ p.support.card := by
  classical
  have h : ∑ q ∈ p.cycleFactorsFinset, 2 ≤ ∑ q ∈ p.cycleFactorsFinset, q.support.card := by
    apply Finset.sum_le_sum
    intro q hq
    exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1.two_le_card_support
  rw [cycle_support_card_sum] at h
  simpa [Nat.mul_comm] using h


end LX.Core.FiniteCuts

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

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The extreme-coordinate bound forces exactly h pairs' worth of moved vertices. -/
theorem solution {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1))
    (hext : ((Finset.univ.filter (fun i => d i= -h)).card : ℤ) ≤ (n : ℤ)-2*h) :
    let q := shiftedLiftPermutation p c h
    (q.support.card : ℤ)=2*h ∧ (q.cycleFactorsFinset.card : ℤ)=h ∧
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ)=h := by
  dsimp only
  let q := shiftedLiftPermutation p c h
  have hr := shifted_capacity_equality hd h hband heq
  change (q.support.card : ℤ)-(q.cycleFactorsFinset.card : ℤ)=h ∧
    (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ)=h at hr
  have hf : (q.support.card : ℤ)+((Finset.univ.filter (fun i => d i= -h)).card : ℤ)=n := by
    exact_mod_cast shifted_support_add_extreme_count hd h hband
  have hc : 2*(q.cycleFactorsFinset.card : ℤ) ≤ (q.support.card : ℤ) := by
    exact_mod_cast twice_cycle_count_le_support q
  change (q.support.card : ℤ)=2*h ∧ (q.cycleFactorsFinset.card : ℤ)=h ∧
    (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ)=h
  omega
