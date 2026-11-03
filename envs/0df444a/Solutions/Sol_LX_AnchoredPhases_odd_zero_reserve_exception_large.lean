-- Prove2me | solution 1 for LX.AnchoredPhases.odd_zero_reserve_exception_large
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:36:59.690457+00:00
-- url     : https://prove2.me/submissions/d8a8bae1-04d5-4854-b0a2-a744e1183d1d

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
import Definitions.Def_LX_AnchorReserveRigidity
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_DepthCrowding
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_global_rank_peak_reserve
import Theorems.Thm_LX_AnchoredPhases_low_forward_depth_paid
import Theorems.Thm_LX_AnchoredPhases_odd_reflection_neighbor_fiber
import Theorems.Thm_LX_AnchoredPhases_rank_peak_next_depth

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
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



/-- Critical parity cases spend a quadratic amount of the actual reserve. -/
theorem critical_rank_peak_reserve (p : State n) (a t : Fin n)
    (ha : GlobalMinimum p a) (e : ℕ) (hn : n=2*height p a+2+e) :
    rankSurplus p a t.val*(rankSurplus p a t.val-1-e) ≤ anchorReserve p a := by
  have hh := global_rank_peak_reserve p a t ha
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
  rw [hn'] at hh
  convert hh using 1
  ring



end LX.AnchoredPhases

end

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The two exceptions to deleting a crossing are paid at their last
minimum-height representative. Its finishing gap is m+3 and its next-depth
count is at most seven. -/
theorem solution (p : State n) (a r u : Fin n)
    (ha : GlobalMinimum p a) (hz : anchorReserve p a=0)
    (m : ℕ) (hn : n=2*m+1) (hh : height p a+1=m) (hm : 4 ≤ m)
    (hu : permutation p a u=u)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (hcase : (r.val=m ∧ u.val=m+1) ∨ (r.val=m+1 ∧ u.val=1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  let c : Fin n := ⟨m+2,by omega⟩
  have hcval : c.val=m+2 := rfl
  have huv : (u+1).val=u.val+1 := Fin.val_add_one_of_lt' (by rcases hcase with h | h <;> omega)
  have hv : (((m+1 : ℕ) : Fin n)).val=m+1 := Nat.mod_eq_of_lt (by omega)
  have hdval : (u+((m+1 : ℕ) : Fin n)).val=(if u.val=1 then m+2 else 1) := by
    rw [Fin.val_add,hv]
    rcases hcase with h | h
    · rw [h.2,ite_eq_right (by omega : m+1 ≠ 1)]
      have he : m+1+(m+1)=n+1 := by omega
      rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_eq_of_lt (by omega : 1<n)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [h.2,ite_eq_left rfl,Nat.mod_eq_of_lt (by omega : 1+(m+1)<n)]
      omega
  have hrawu : p u-u=p a-a := by
    change p u+(a-p a)=u at hu
    linear_combination hu
  have hrawc : p c-c=p a-a := by
    rw [← hrawu]
    apply (odd_reflection_neighbor_fiber p r u hp m hn (by omega) c).mpr
    rcases hcase with h | h
    · exact Or.inr (Or.inl (Fin.ext (by omega)))
    · apply Or.inr
      apply Or.inr
      apply Fin.ext
      rw [hdval,ite_eq_left h.2]
  have hch : height p c=height p a := by
    have hperm : permutation p c=permutation p a := by
      apply Equiv.ext
      intro j
      change p j+(c-p c)=p j+(a-p a)
      linear_combination -hrawc
    exact congrArg (fun q : State n => (descendingPositions q).card) hperm
  have hfiber (i : Fin n) (hi : p i-i=p a-a) : 0 < i.val ∧ i.val ≤ c.val := by
    have hf := (odd_reflection_neighbor_fiber p r u hp m hn (by omega) i).mp (hi.trans hrawu.symm)
    rcases hf with rfl | rfl | rfl
    · rcases hcase with h | h <;> omega
    · rcases hcase with h | h <;> omega
    · rw [hdval]
      split_ifs <;> omega
  have hhead : p 0 ≠ p c-c := by
    intro he
    have hf := hfiber 0 (by simpa using he.trans hrawc)
    simp only [Fin.val_zero] at hf
    omega
  have hlast (i : Fin n) (hi : p i-i=p c-c) : i.val ≤ c.val := (hfiber i (hi.trans hrawc)).2
  have hpc : (p c).val=n-1 := by
    rcases hcase with h | h
    · have hcv : c=u+1 := Fin.ext (by omega)
      have hpv : p (u+1)=r-u := by simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left] using hp u
      have hlt : r < u := by change r.val < u.val; omega
      rw [hcv,hpv,Fin.coe_sub_iff_lt.mpr hlt]
      omega
    · have hcu : c ≠ u := by intro he; have := congrArg Fin.val he; omega
      have hcv : c ≠ u+1 := by intro he; have := congrArg Fin.val he; omega
      have hpc' : p c=r-c := by
        simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hcu hcv] using hp c
      have hlt : r < c := by change r.val < c.val; omega
      rw [hpc',Fin.coe_sub_iff_lt.mpr hlt]
      omega
  have hgap : (c-p c).val=m+3 := by
    rw [Fin.coe_sub_iff_lt.mpr (show c < p c from by change c.val < (p c).val; omega)]
    omega
  have hR (t : Fin n) : rankSurplus p a t.val ≤ 2 := by
    have hb := critical_rank_peak_reserve p a t ha 1 (by omega)
    rw [hz] at hb
    norm_num at hb
    by_contra hnot
    have hp : 3 ≤ rankSurplus p a t.val := by omega
    nlinarith only [hb,hp,sq_nonneg (rankSurplus p a t.val-2)]
  have hd := rank_peak_next_depth p a 2 hR c (by omega)
  obtain ⟨w,hw,hprice⟩ := low_forward_depth_paid p c (by omega) (Or.inr (by omega))
    hhead hlast (by omega) (by omega) (by omega)
  exact ⟨w,hw,by omega⟩
