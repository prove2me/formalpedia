-- Prove2me | solution 1 for LX.CycleGeometry.single_three_neighbor_reflection_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:46:40.971596+00:00
-- url     : https://prove2.me/submissions/723854d9-b6c5-431c-b670-cb3124a34d65

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
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_PairCoreGeometry
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_Core_FiniteCuts_adjacent_swap_inversion_price
import Theorems.Thm_LX_Core_FiniteCuts_finite_shallow_matching_noncrossing
import Theorems.Thm_LX_Core_FiniteCuts_fixed_count_two_reflection
import Theorems.Thm_LX_CycleGeometry_consecutive_three_swap_mass
import Theorems.Thm_LX_CycleGeometry_single_three_consecutive_at_zero

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



/-- The same raising adjacent exchange has exact inversion cost one. -/
theorem adjacent_raising_inversion_price (p : State n) (a b : Fin n)
    (hadj : b.val=a.val+1) (hp : (p a).val < (p b).val) :
    inversionNumber (p*Equiv.swap a b)=inversionNumber p+1 := by
  have hh := adjacent_swap_inversion_price (p*Equiv.swap a b) a b hadj (by
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using hp)
  have he : p*Equiv.swap a b*Equiv.swap a b=p := by simp [mul_assoc]
  rw [he] at hh
  exact hh.symm



end LX.Core.FiniteCuts

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

theorem fixed_positions_card (p : State n) :
    ((fixedPositions p).card : ℤ)=(n : ℤ)-(p.support.card : ℤ) := by
  have hs : fixedPositions p=Finset.univ \ p.support := by
    ext i
    simp [Equiv.Perm.mem_support]
  have hc : p.support.card ≤ n := by simpa using p.support.card_le_univ
  rw [hs,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hc]







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

/-- Splitting the consecutive 3-cycle yields an actual noncrossing matching
with two fixed positions. The existing matching classification identifies
the entire input as a reflection with one neighboring swap. -/
theorem solution (q : State n) (hq : cycleDefect q=0)
    (he : q.support.card=2*q.cycleFactorsFinset.card+1) (hzero : q 0=0)
    (hfixed : ∀ i : Fin n,q i=i → i=0)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) :
    ∃ a b : Fin n,a.val+1=b.val ∧ ∀ i : Fin n,(q*Equiv.swap a b) i= -i := by
  classical
  obtain ⟨a,b,c,hab,hbc,ha,hb,hc,houtside⟩ := single_three_consecutive_at_zero q hq he hfixed hback
  have habn : a ≠ b := by intro h; have := congrArg Fin.val h; omega
  have hacn : a ≠ c := by intro h; have := congrArg Fin.val h; omega
  have hbcn : b ≠ c := by intro h; have := congrArg Fin.val h; omega
  have ha0 : a ≠ 0 := by
    intro h
    have ha' := ha
    rw [h,hzero] at ha'
    have := congrArg Fin.val ha'
    have := congrArg Fin.val h
    omega
  have hb0 : b ≠ 0 := by
    intro h
    rw [h,Fin.val_zero] at hab
    omega
  let Q := q*Equiv.swap a b
  have hQa : Q a=c := by simp only [Q,Equiv.Perm.mul_apply,Equiv.swap_apply_left,hb]
  have hQb : Q b=b := by simp only [Q,Equiv.Perm.mul_apply,Equiv.swap_apply_right,ha]
  have hQi (i : Fin n) (hia : i ≠ a) (hib : i ≠ b) : Q i=q i := by
    simp only [Q,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hia hib]
  have hQc : Q c=a := (hQi c hacn.symm hbcn.symm).trans hc
  have himage (i : Fin n) (hia : i ≠ a) (hib : i ≠ b) (hic : i ≠ c) :
      q i ≠ a ∧ q i ≠ b ∧ q i ≠ c := by
    exact ⟨fun h => hic (q.injective (h.trans hc.symm)),
      fun h => hia (q.injective (h.trans ha.symm)),
      fun h => hib (q.injective (h.trans hb.symm))⟩
  have hinv : Function.Involutive Q := by
    intro i
    by_cases hia : i=a
    · subst i; rw [hQa,hQc]
    by_cases hib : i=b
    · subst i; rw [hQb,hQb]
    by_cases hic : i=c
    · subst i; rw [hQc,hQa]
    have hi := himage i hia hib hic
    rw [hQi i hia hib,hQi (q i) hi.1 hi.2.1]
    exact houtside i hia hib hic
  have hfOld : fixedPositions q={0} := by
    ext i
    simp only [mem_fixedPositions,Finset.mem_singleton]
    exact ⟨hfixed i,fun h => by rw [h,hzero]⟩
  have hfNew : fixedPositions Q={0,b} := by
    ext i
    simp only [mem_fixedPositions,Finset.mem_insert,Finset.mem_singleton]
    by_cases hia : i=a
    · subst i
      simp [hQa,hacn.symm,ha0,habn]
    by_cases hib : i=b
    · subst i
      simp [hQb]
    rw [hQi i hia hib]
    constructor
    · intro hi
      exact Or.inl (hfixed i hi)
    · rintro (hi | hi)
      · rw [hi,hzero]
      · exact False.elim (hib hi)
  have hfc : (fixedPositions Q).card=2 := by rw [hfNew]; simp [hb0.symm]
  have hsOld := fixed_positions_card q
  rw [hfOld] at hsOld
  simp only [Finset.card_singleton,Nat.cast_one] at hsOld
  have hsNew := fixed_positions_card Q
  rw [hfc] at hsNew
  have hs : Q.support.card=2*q.cycleFactorsFinset.card := by omega
  have hmass := consecutive_three_swap_mass q a b c hab hbc ha hb
  have hI := adjacent_raising_inversion_price q a b hab.symm (by rw [ha,hb]; omega)
  have hdef : (∑ i, |_root_.LX.Core.FiniteCuts.displacement Q i|)-(inversionNumber Q : ℤ)=
      (q.cycleFactorsFinset.card : ℤ) := by
    change (∑ i, |_root_.LX.Core.FiniteCuts.displacement (q*Equiv.swap a b) i|)-(inversionNumber (q*Equiv.swap a b) : ℤ)=_
    rw [hmass,hI]
    unfold cycleDefect at hq
    rw [he] at hq
    push_cast at *
    omega
  have hnc : NoncrossingPairs Q := finite_shallow_matching_noncrossing Q _ hs hdef
  have hQzero : Q 0=0 := (hQi 0 ha0.symm hb0.symm).trans hzero
  have hnoadj (i : Fin n) : i.val+1 ≠ (Q i).val := by
    intro hi
    by_cases hia : i=a
    · subst i; rw [hQa] at hi; omega
    by_cases hib : i=b
    · subst i; rw [hQb] at hi; omega
    by_cases hic : i=c
    · subst i; rw [hQc] at hi; omega
    rw [hQi i hia hib] at hi
    exact hback i (q i) hi (houtside i hia hib hic)
  exact ⟨a,b,hab,fixed_count_two_reflection Q hinv hnc hQzero hfc hnoadj⟩
