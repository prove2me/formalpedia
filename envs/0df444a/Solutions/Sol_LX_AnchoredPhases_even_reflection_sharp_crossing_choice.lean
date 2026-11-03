-- Prove2me | solution 1 for LX.AnchoredPhases.even_reflection_sharp_crossing_choice
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:23:57.174193+00:00
-- url     : https://prove2.me/submissions/0a3eb970-7c89-49e3-8c1c-0e953ad5c7db

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
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_doubled_residue_cases

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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
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
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Two consecutive anchors cannot both miss the chosen neighboring pair.
The two excluded residues are 0 and 1, while an anchor step adds 2. -/
theorem reflection_two_anchor_choice (hn : 4 ≤ n) (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a i : Fin n) :
    ∃ b : Fin n,(b=a ∨ b=a+1) ∧ 2 ≤ (cyclicOffset p b i).val := by
  by_cases ha : 2 ≤ (cyclicOffset p a i).val
  · exact ⟨a,Or.inl rfl,ha⟩
  · refine ⟨a+1,Or.inr rfl,?_⟩
    have he : cyclicOffset p (a+1) i=cyclicOffset p a i+2 := by
      unfold cyclicOffset
      simp only [hp]
      ring
    have hv : (2 : Fin n).val=2 := by norm_num [Nat.mod_eq_of_lt (by omega : 2 < n)]
    rw [he,Fin.val_add,hv,Nat.mod_eq_of_lt (by omega)]
    omega






end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem solution (p : State n) (r i : Fin n)
    (hp : ∀ j,p j=r-j) (m : ℕ) (hn : n=2*m) (hm : 4 ≤ m) :
    (∃ a : Fin n,m < a.val ∧ a.val+(-p a).val ≤ n+3 ∧
      2 ≤ (cyclicOffset p a i).val) ∨
      (r=0 ∧ (i.val=1 ∨ i.val=m+1)) := by
  have hneg (j : Fin n) : -p j=j-r := by rw [hp]; abel
  have hdouble : (m : Fin n)+(m : Fin n)=0 := by
    have he := congrArg (fun k : ℕ => (k : Fin n)) hn
    simp only [Nat.cast_mul,Nat.cast_ofNat,Fin.natCast_self] at he
    linear_combination -he
  by_cases hr0 : r=0
  · let a : Fin n := ⟨m+1,by omega⟩
    have hav : a.val=m+1 := rfl
    have hfinish : a.val+(-p a).val ≤ n+3 := by
      rw [hneg,hr0,sub_zero]
      omega
    by_cases hcross : 2 ≤ (cyclicOffset p a i).val
    · exact Or.inl ⟨a,by omega,hfinish,hcross⟩
    have heven : Even (cyclicOffset p a i) := by
      refine ⟨a-i,?_⟩
      unfold cyclicOffset
      simp only [hp]
      ring
    have hmod := (Fin.even_iff_mod_of_even (show Even n from ⟨m,by omega⟩)).mp heven
    have hz : cyclicOffset p a i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have htwice : i+i=a+a := by
      unfold cyclicOffset at hz
      simp only [hp] at hz
      linear_combination -hz
    have hcases := doubled_residue_cases i a htwice
    have hi := i.isLt
    exact Or.inr ⟨hr0,by omega⟩
  by_cases hrlast : r.val=n-1
  · let a : Fin n := ⟨m+1,by omega⟩
    have hav : a.val=m+1 := rfl
    have hfinish : a.val+(-p a).val ≤ n+3 := by
      rw [hneg,Fin.coe_sub_iff_lt.mpr (show a < r from by change a.val < r.val; omega)]
      omega
    have hfinishr : r.val+(-p r).val ≤ n+3 := by simp [hp]; have := r.isLt; omega
    by_cases hcross : 2 ≤ (cyclicOffset p a i).val
    · exact Or.inl ⟨a,by omega,hfinish,hcross⟩
    have hcrossr : 2 ≤ (cyclicOffset p r i).val := by
      by_contra hnot
      have hrfin : r+1=0 := by
        have he : ((r.val+1 : ℕ) : Fin n)=0 := by rw [show r.val+1=n by omega]; simp
        simpa only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_one] using he
      have hafin : a=(m : Fin n)+1 := by
        apply Fin.ext
        change m+1=(m%n+1%n)%n
        rw [Nat.mod_eq_of_lt (by omega : m<n),Nat.mod_eq_of_lt (by omega : 1<n),Nat.mod_eq_of_lt (by omega)]
      have he : cyclicOffset p a i=cyclicOffset p r i+4 := by
        unfold cyclicOffset
        simp only [hp,hafin]
        linear_combination hdouble-2*hrfin
      have hv := congrArg Fin.val he
      have hv4 : (4 : Fin n).val=4 := by norm_num [Nat.mod_eq_of_lt (by omega : 4<n)]
      rw [Fin.val_add,hv4,Nat.mod_eq_of_lt (by omega)] at hv
      omega
    exact Or.inl ⟨r,by omega,hfinishr,hcrossr⟩
  · let a : Fin n := ⟨max (m+1) r.val,by have := r.isLt; omega⟩
    have hav : a.val=max (m+1) r.val := rfl
    have hbval : (a+1).val=max (m+1) r.val+1 := by
      rw [Fin.val_add_one_of_lt' (by have := r.isLt; omega : a.val+1<n),hav]
    have hrpos : 0 < r.val := Fin.pos_iff_ne_zero.mpr hr0
    have hgood (j : Fin n) (hj : j.val=max (m+1) r.val ∨ j.val=max (m+1) r.val+1) :
        m < j.val ∧ j.val+(-p j).val ≤ n+3 := by
      have hjr : r ≤ j := by change r.val ≤ j.val; omega
      rw [hneg,Fin.coe_sub_iff_le.mpr hjr]
      have := r.isLt
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg := hgood b (by rcases hb with rfl | rfl; exact Or.inl hav; exact Or.inr hbval)
    exact Or.inl ⟨b,hg.1,hg.2,hcross⟩
