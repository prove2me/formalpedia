-- Prove2me | solution 1 for LX.AnchoredPhases.odd_maximal_minima_complete
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:17:55.389115+00:00
-- url     : https://prove2.me/submissions/e3ec1b58-1b32-420f-bfdd-2185b47109ec

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_ClockwiseLiftCount
import Definitions.Def_LX_CompleteMapping
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_recover_global_minimum
import Theorems.Thm_LX_AnchoredPhases_zero_slack_phase

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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators







theorem canonical_lift {n : ℕ} (p : State n) :
    IsLift p 0 (fun i => (p.symm i : ℤ) - (i : ℤ)) := by
  constructor
  · rw [Finset.sum_sub_distrib]
    have h := Equiv.sum_comp p.symm (fun i : Fin n => (i : ℤ))
    rw [h]
    simp
  · intro i
    simp [Int.ModEq]

/-- Existence uses well-ordering of natural energy, even though the space of
phases and integer lift vectors is infinite. -/
theorem exists_minimal {n : ℕ} (p : State n) :
    ∃ c d, IsLift p c d ∧ ∀ c' d', IsLift p c' d' → energy d ≤ energy d' := by
  classical
  let P : ℕ → Prop := fun k => ∃ c d, IsLift p c d ∧ energy d = k
  have hex : ∃ k, P k := ⟨_, 0, _, canonical_lift p, rfl⟩
  obtain ⟨c, d, hd, he⟩ := Nat.find_spec hex
  refine ⟨c, d, hd, ?_⟩
  intro c' d' hd'
  rw [he]
  exact Nat.find_min' hex ⟨c', d', hd', rfl⟩


















end LX.Core.AffineLift

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
/-! Displacements of finite permutations define balanced affine lifts.
The canonical finite lift has phase zero. -/
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {b : ℕ}



theorem canonical_lift (p : State b) : AffineLift.IsLift p.symm 0 (_root_.LX.Core.FiniteCuts.displacement p) := by
  unfold _root_.LX.Core.FiniteCuts.displacement
  simpa only [Equiv.symm_symm] using AffineLift.canonical_lift p.symm


end LX.Core.FiniteCuts

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









theorem clockwise_representative_mass (p : State n) :
    (∑ i : Fin n, (clockwiseRepresentative p i-(i : ℤ))) =
      (n : ℤ)*((descendingPositions p).card : ℤ) := by
  have hp : (∑ i : Fin n, _root_.LX.Core.FiniteCuts.displacement p i)=0 := (canonical_lift p).1
  have hpoint (i : Fin n) : clockwiseRepresentative p i-(i : ℤ) =
      _root_.LX.Core.FiniteCuts.displacement p i+(if (p i).val < i.val then (n : ℤ) else 0) := by
    unfold clockwiseRepresentative _root_.LX.Core.FiniteCuts.displacement
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, hp, zero_add]
  rw [← Finset.sum_filter]
  simp [descendingPositions, mul_comm]




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
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]









theorem permutation_anchor (p : State n) (a : Fin n) : permutation p a a = a := by
  simp [permutation]

theorem displacement_balance (p : State n) (a : Fin n) : ∑ i, _root_.LX.AnchoredPhases.displacement p a i = 0 := by
  unfold _root_.LX.AnchoredPhases.displacement
  rw [Finset.sum_sub_distrib, clockwise_representative_mass]
  simp [height]



theorem displacement_anchor (p : State n) (a : Fin n) :
    _root_.LX.AnchoredPhases.displacement p a a = -(height p a : ℤ) := by
  simp [_root_.LX.AnchoredPhases.displacement, clockwiseRepresentative, permutation_anchor]
















end LX.AnchoredPhases

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]







/-- The finite anchor family contains a globally energy-minimal actual lift. -/
theorem exists_global_minimum (p : State n) : ∃ a : Fin n, GlobalMinimum p a := by
  obtain ⟨c,d,hd,hm⟩ := exists_minimal p.symm
  obtain ⟨a,_,_,ha⟩ := recover_global_minimum hd hm
  exact ⟨a,ha⟩









end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- If every global minimum in odd dimension has maximal height, the
singleton minimum is tight and advances the minimum phase by one offset.
The resulting orbit contains every residue, forcing a complete mapping. -/
theorem solution (p : State n) (m : ℕ) (hn : n=2*m+1)
    (hheight : ∀ a : Fin n,GlobalMinimum p a → height p a=m) : CompleteMapping p := by
  have hstep (a : Fin n) (ha : GlobalMinimum p a) :
      ∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+1 := by
    have hh := hheight a ha
    let S := (Finset.univ : Finset (Fin n)).erase a
    have hcard : S.card=n-1 := by simp [S]
    have hsum : (∑ i ∈ S,_root_.LX.AnchoredPhases.displacement p a i)=(m : ℤ) := by
      have hs := Finset.sum_erase_add Finset.univ (_root_.LX.AnchoredPhases.displacement p a) (Finset.mem_univ a)
      rw [displacement_balance,displacement_anchor,hh] at hs
      change (∑ i ∈ S,_root_.LX.AnchoredPhases.displacement p a i)+ -(m : ℤ)=0 at hs
      omega
    have htight : 2*(∑ i ∈ S,_root_.LX.AnchoredPhases.displacement p a i)=(S.card : ℤ)*((n : ℤ)-S.card) := by
      rw [hsum,hcard,Nat.cast_sub (NeZero.pos n)]
      norm_num only [Nat.cast_one]
      have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
      nlinarith
    obtain ⟨b,hb,_,hphase,_⟩ := zero_slack_phase ha S htight
    have hbheight := hheight b hb
    rw [hcard,Nat.cast_sub (NeZero.pos n),Fin.natCast_self,Nat.cast_one] at hphase
    simp only [phase,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,hh,hbheight] at hphase
    exact ⟨b,hb,by linear_combination -hphase⟩
  obtain ⟨a,ha⟩ := exists_global_minimum p
  have hiter : ∀ k : ℕ,∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+(k : Fin n) := by
    intro k
    induction k with
    | zero => exact ⟨a,ha,by simp⟩
    | succ k ih =>
      obtain ⟨b,hb,hbr⟩ := ih
      obtain ⟨c,hc,hcr⟩ := hstep b hb
      refine ⟨c,hc,?_⟩
      rw [hcr,hbr,Nat.cast_add,Nat.cast_one]
      ring
  apply Finite.injective_iff_surjective.mpr
  intro r
  obtain ⟨b,_,hbr⟩ := hiter (r-(p a-a)).val
  simp only [Fin.cast_val_eq_self] at hbr
  exact ⟨b,by linear_combination hbr⟩
