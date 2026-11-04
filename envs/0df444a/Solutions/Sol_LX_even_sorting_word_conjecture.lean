-- Prove2me | solution 1 for LX.even_sorting_word_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-03T08:00:47.899879+00:00
-- url     : https://prove2.me/submissions/2362e5cb-9d4c-454c-bd2c-0509d06c871e

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
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_MinimumHeightRanks
import Definitions.Def_LX_PairCoreGeometry
import Definitions.Def_LX_PermutationCode
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_ReverseDual
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_AnchoredPhases_conjecture_unpaid_reserve_geometry
import Theorems.Thm_LX_AnchoredPhases_even_unpaid_head_pattern
import Theorems.Thm_LX_Core_WordReflection_mirror_letter_eval

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Antipode
end LX.Antipode
namespace LX.CenteredLift
end LX.CenteredLift
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.EventGeometry
end LX.EventGeometry
namespace LX.FiniteDropBudget
end LX.FiniteDropBudget
namespace LX.FiniteJoin
end LX.FiniteJoin
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace LX.MatchingGeometry
end LX.MatchingGeometry
namespace LX.PairCore
end LX.PairCore
namespace LX.Small4
end LX.Small4
namespace LX.Small5
end LX.Small5
namespace LX.Small6
end LX.Small6
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

section
/-! A constructive enumeration of permutations. Checking one word per code
avoids a quadratic search through a finite set of evaluated words. -/
namespace LX.Core









@[simp] theorem decode_encode {n : ℕ} (p : State n) : decode (encode p) = p := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih => simp only [encode, decode, ih, Prod.mk.eta, Equiv.symm_apply_apply]




end LX.Core

end

section
namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]





theorem even_global_unpaid_head_pattern (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12) : p 0=0 ∧ p 1= -1 := by
  have hbase : 3*(n : ℤ)^2-8*n+12=4*(3*(m : ℤ)^2-4*m+3) := by
    have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
    rw [hn']; ring
  have hstrict : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(0 : ℤ)) := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w,hw,by omega⟩
  obtain ⟨a,_,_,hnlarge,_,hh,hmin,_⟩ :=
    conjecture_unpaid_reserve_geometry hn4 p m 0 (by omega) (by omega) hstrict
  exact even_unpaid_head_pattern p a (by omega) (by omega) hmin hunpaid




end LX.AnchoredPhases

end

section
/-! Reflection in the edge between positions zero and one. It exchanges L/R,
fixes X, and agrees with the word symmetry already used by the lower proof. -/
namespace LX.Core.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



@[simp] theorem reflection_apply (i : Fin n) : reflection i=1-i := rfl

@[simp] theorem reflection_twice (i : Fin n) : reflection (reflection i)=i := by
  simp only [reflection_apply]
  abel

@[simp] theorem reflection_square : (reflection : State n)*reflection=1 := by
  apply Equiv.ext
  intro i
  exact reflection_twice i



end LX.Core.WordReflection

end

section
namespace LX
open LX.Core.WordReflection
variable {n : ℕ} [NeZero n]



 theorem _root_.LX.UploadHelpers.ReverseDual.reflection_inv : (reflection : State n)⁻¹=reflection := by
  apply Equiv.ext
  intro i
  rfl

@[simp] theorem reverseDual_one : reverseDual (1 : State n)=1 := by
  simp [reverseDual]

theorem reverseDual_mul (p q : State n) : reverseDual (p*q)=reverseDual q*reverseDual p := by
  simp only [reverseDual,mul_inv_rev]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul]

@[simp] theorem reverseDual_twice (p : State n) : reverseDual (reverseDual p)=p := by
  simp only [reverseDual,mul_inv_rev,_root_.LX.UploadHelpers.ReverseDual.reflection_inv,inv_inv]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul,mul_one]

theorem reverseDual_letter (c : Letter) : reverseDual (eval (n := n) [c])=eval [c] := by
  have he : (eval (n := n) [c])⁻¹=reflection*eval [c]*reflection := by
    simpa only [eval,List.map_cons,List.map_nil,LX.Core.eval_cons,LX.Core.eval_nil,mul_one,
      LX.Core.Letter.eval_inverse] using mirror_letter_eval (n := n) c.toCore
  rw [reverseDual,he]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul,mul_one]

theorem eval_reverse_dual (w : List Letter) : eval (n := n) w.reverse=reverseDual (eval w) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.reverse_cons,eval_append,ih]
    have he : eval (n := n) (c::w)=eval [c]*eval w := by
      simpa only [List.singleton_append] using eval_append (n := n) [c] w
    rw [he,reverseDual_mul,reverseDual_letter]

theorem reverse_dual_sorting_word (p : State n) (w : List Letter)
    (hw : reverseDual p*eval w=1) : p*eval w.reverse=1 := by
  have he := congrArg reverseDual hw
  rw [reverseDual_mul,reverseDual_twice,reverseDual_one,← eval_reverse_dual] at he
  exact mul_eq_one_comm.mp he



end LX

end

namespace LX
end LX
open LX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Every even input is sorted at the conjectured constant three. Applying
the necessary head pattern to the mirrored inverse excludes every unpaid
input; no phase-selection premise remains. -/
theorem solution (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
  by_contra hunpaid
  have hp := AnchoredPhases.even_global_unpaid_head_pattern hn4 p m hn hunpaid
  have hdual : ¬ ∃ w : List Letter,reverseDual p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w.reverse,reverse_dual_sorting_word p w hw,by simpa using hprice⟩
  have hq := AnchoredPhases.even_global_unpaid_head_pattern hn4 (reverseDual p) m hn hdual
  have hq0 : (1 : Fin n)-p.symm 1=0 := by
    simpa only [reverseDual,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      LX.Core.WordReflection.reflection_apply,sub_zero] using hq.1
  have hi : p.symm 1=1 := by linear_combination -hq0
  have hp1 : p 1=1 := by
    have he := p.apply_symm_apply 1
    rw [hi] at he
    exact he
  have hone : (1 : Fin n)= -1 := hp1.symm.trans hp.2
  have htwo : (2 : Fin n)=0 := by linear_combination hone
  have hv2 : (2 : Fin n).val=2 := by simp [Nat.mod_eq_of_lt (show 2<n by omega)]
  have hv := congrArg Fin.val htwo
  rw [hv2,Fin.val_zero] at hv
  omega
