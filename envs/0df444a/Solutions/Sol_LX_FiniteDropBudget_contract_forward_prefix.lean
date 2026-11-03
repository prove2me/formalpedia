-- Prove2me | solution 1 for LX.FiniteDropBudget.contract_forward_prefix
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:42:20.469872+00:00
-- url     : https://prove2.me/submissions/1a2ef821-a158-418e-8495-ca4177065c19

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
import Definitions.Def_LX_FiniteDropBudget
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_ForwardPrefixContraction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Theorems.Thm_LX_FiniteDropBudget_head_merge_drops
import Theorems.Thm_LX_FiniteDropBudget_head_merge_inversions
import Theorems.Thm_LX_FiniteDropBudget_head_merge_mass

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
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
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
namespace LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]



theorem head_merge_forward_prefix (p : LX.Core.State n) (r : ℕ)
    (hp : ForwardPrefix p r) (hhead : p 0 ≠ 0) (hb : (p 0).val < r) :
    ForwardPrefix (p*Equiv.swap 0 (p 0)) r := by
  let b := p 0
  let q := p*Equiv.swap 0 b
  have hb0 : 0 < b.val := Fin.pos_iff_ne_zero.mpr hhead
  have hr : 0 < r := by omega
  have hnext : b.val < (p b).val := by
    have hh := (hp b hb).1
    have hn : p b ≠ b := by intro he; exact hhead (p.injective he)
    have hn' : (p b).val ≠ b.val := fun he => hn (Fin.ext he)
    omega
  have hq0 : q 0=p b := by simp [q]
  have hqb : q b=b := by simp [q,b]
  have hqi (i : Fin n) (hi0 : i ≠ 0) (hib : i ≠ b) : q i=p i := by
    simp only [q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hi0 hib]
  intro i hir
  change i.val ≤ (q i).val ∧ _
  by_cases hi0 : i=0
  · subst i
    rw [hq0]
    refine ⟨by simp,?_⟩
    intro j hj0 hjn
    have hj0' : j ≠ 0 := Fin.ne_of_val_ne (by simpa using Nat.ne_of_gt hj0)
    by_cases hjb : j=b
    · exact hjb ▸ hqb
    rw [hqi j hj0' hjb]
    by_cases hjlt : j.val < b.val
    · exact (hp 0 (by simpa using hr)).2 j hj0 hjlt
    · have hjne : j.val ≠ b.val := fun he => hjb (Fin.ext he)
      exact (hp b hb).2 j (by omega) hjn
  by_cases hib : i=b
  · subst i
    rw [hqb]
    exact ⟨le_rfl,fun j h1 h2 => by omega⟩
  rw [hqi i hi0 hib]
  refine ⟨(hp i hir).1,?_⟩
  intro j hij hjp
  have hj0 : j ≠ 0 := by intro he; subst j; simp at hij
  by_cases hjb : j=b
  · exact hjb ▸ hqb
  rw [hqi j hj0 hjb]
  exact (hp i hir).2 j hij hjp





end LX.FiniteDropBudget

end

namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
open LX
open LX.FiniteDropBudget
open scoped BigOperators
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- An ascending prefix chain can be merged into the head. All its other
vertices become fixed, without increasing mass minus inversions. -/
theorem solution (p : LX.Core.State n) (r : ℕ) (hr : 0 < r)
    (hp : ForwardPrefix p r) (hhead : p 0 ≠ 0) :
    ∃ q : LX.Core.State n,
      (∀ i : Fin n,0 < i.val → i.val < r → q i=i) ∧
      ForwardPrefix q r ∧ q 0 ≠ 0 ∧
      descendingPositions q=descendingPositions p ∧ backwardUnits q=backwardUnits p ∧
      (∑ i, |_root_.LX.Core.FiniteCuts.displacement q i|)-(inversionNumber q : ℤ) ≤
        (∑ i, |_root_.LX.Core.FiniteCuts.displacement p i|)-(inversionNumber p : ℤ) := by
  generalize he : n-(p 0).val=k
  induction k using Nat.strong_induction_on generalizing p with
  | h k ih =>
    by_cases hb : r ≤ (p 0).val
    · refine ⟨p,?_,hp,hhead,rfl,rfl,le_rfl⟩
      intro i hi0 hir
      exact (hp 0 (by simpa using hr)).2 i (by simpa using hi0) (by omega)
    let b := p 0
    have hbpos : 0 < b.val := Fin.pos_iff_ne_zero.mpr hhead
    have hbr : b.val < r := by omega
    have hnext : b.val < (p b).val := by
      have hh := (hp b hbr).1
      have hn : p b ≠ b := by intro he; exact hhead (p.injective he)
      have hn' : (p b).val ≠ b.val := fun he => hn (Fin.ext he)
      omega
    let t := p*Equiv.swap 0 b
    have ht0 : t 0=p b := by simp [t]
    have htpre : ForwardPrefix t r := head_merge_forward_prefix p r hp hhead hbr
    have hthead : t 0 ≠ 0 := by
      intro hz
      have hv := congrArg Fin.val hz
      rw [ht0,Fin.val_zero] at hv
      exact (Nat.ne_of_gt (lt_trans hbpos hnext)) hv
    have hk : n-(t 0).val < k := by rw [ht0]; have := (p b).isLt; omega
    obtain ⟨q,hqfix,hqpre,hqhead,hqd,hqu,hqcost⟩ :=
      ih (n-(t 0).val) hk t htpre hthead rfl
    have htd := head_merge_drops p b hbpos rfl hnext
    have htm := head_merge_mass p b hbpos rfl hnext
    have hti := head_merge_inversions p b hbpos rfl hnext
      (fun j hj0 hjb => (hp 0 (by simpa using hr)).2 j (by simpa using hj0) hjb)
    refine ⟨q,hqfix,hqpre,hqhead,hqd.trans htd.1,hqu.trans htd.2,?_⟩
    change (∑ i, |_root_.LX.Core.FiniteCuts.displacement t i|)=_ at htm
    change inversionNumber t=inversionNumber p+1 at hti
    rw [htm,hti] at hqcost
    push_cast at hqcost
    omega
