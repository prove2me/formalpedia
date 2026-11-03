-- Prove2me | solution 1 for LX.diameter_conjecture_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:26:22.150197+00:00
-- url     : https://prove2.me/submissions/2b8972d3-65e4-4739-ae0c-1a2e89aecc4c

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
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_AntipodeCandidates
import Definitions.Def_LX_Connected
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_PermutationCode
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_Small5Exact
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_AffineScan_ScanTrace_exchange_count
import Theorems.Thm_LX_AffineScan_sorting_word_of_zero
import Theorems.Thm_LX_Antipode_even_greedy_price_lower
import Theorems.Thm_LX_Antipode_odd_greedy_price_lower
import Theorems.Thm_LX_exists_shortest_bounded_greedy_word
import Theorems.Thm_LX_length_lower_iff_greedy_prices

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
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
namespace LX.Small5
end LX.Small5
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

theorem Letter.eval_mem {n : ℕ} [NeZero n] (a : Letter) :
    a.eval (n := n) ∈ generators n := by
  cases a <;> simp [Letter.eval, generators]




end LX.Core

end

section
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h

theorem lift_residue {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (i : Fin n) :
    i + (d i : Fin n) = p.symm i + (c : Fin n) := by
  have h := cast_eq_of_modEq (hd.2 i)
  simpa using h


















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

end

section
namespace LX.Core



theorem connected_of_generates {G : Type*} [Group G] (S : Set G)
    (hgen : Subgroup.closure S = ⊤) : (SimpleGraph.mulCayley S).Connected := by
  have hsub : Subgroup.closure S ≤ reachableSubgroup S := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change (SimpleGraph.mulCayley S).Reachable 1 g
    by_cases h : 1 = g
    · rw [← h]
    · exact ((SimpleGraph.mulCayley_adj' S 1 g).mpr
        ⟨h, g, hg, Or.inl (one_mul g)⟩).reachable
  rw [hgen] at hsub
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  exact ⟨1, fun g => hsub (Subgroup.mem_top g)⟩

theorem generators_closure (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    Subgroup.closure (generators n) = ⊤ := by
  have hrot : L n (0 : Fin n) = 1 := by
    cases n with
    | zero => omega
    | succ k => exact finRotate_apply_zero
  have hgen := Equiv.Perm.closure_cycle_adjacent_swap
    (isCycle_finRotate_of_le hn)
    (support_finRotate_of_le hn) (0 : Fin n)
  change Subgroup.closure ({L n, Equiv.swap 0 (L n 0)} : Set (State n)) = ⊤ at hgen
  rw [hrot] at hgen
  apply top_unique
  rw [← hgen]
  apply Subgroup.closure_mono
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> simp [generators, X]

theorem connected (n : ℕ) [NeZero n] (hn : 2 ≤ n) : (graph n).Connected :=
  connected_of_generates _ (generators_closure n hn)


end LX.Core

end

section
/-! A zero-displacement phase lift is an actual rotation. Its final rotation
is explicitly paid by an LX.Core word of length at most n-1. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_power_apply (k : ℕ) (i : Fin n) : (L n ^ k) i = i + (k : Fin n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [L, finRotate_apply, Nat.cast_add, add_comm, add_left_comm]


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
/-! The cyclic generator has period `n`.
This identity allows inverse rotations to be expanded into forward words. -/
namespace LX.Core.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_period : L n ^ n=1 := by
  apply Equiv.ext
  intro i
  simp [AffineLift.rotation_power_apply]


end LX.Core.RotationWords

end

section
namespace LX.Core



@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]

theorem generator_is_letter {n : ℕ} [NeZero n] {g : State n}
    (hg : g ∈ generators n) : ∃ c : Letter, c.eval = g := by
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨.l, rfl⟩
  · exact ⟨.r, rfl⟩
  · exact ⟨.x, rfl⟩

theorem adj_iff_letter {n : ℕ} [NeZero n] (a b : State n) :
    (graph n).Adj a b ↔ a ≠ b ∧ ∃ c : Letter, a * c.eval = b := by
  rw [graph, SimpleGraph.mulCayley_adj']
  constructor
  · rintro ⟨hne, g, hg, h⟩
    obtain ⟨c, rfl⟩ := generator_is_letter hg
    refine ⟨hne, ?_⟩
    rcases h with h | h
    · exact ⟨c, h⟩
    · refine ⟨c.inverse, ?_⟩
      rw [Letter.eval_inverse, h, mul_inv_cancel_right]
  · rintro ⟨hne, c, hc⟩
    exact ⟨hne, c.eval, c.eval_mem, Or.inl hc⟩

/-- Every graph walk has a literal L/R/X word of exactly the same length. -/
theorem word_of_walk {n : ℕ} [NeZero n] {a b : State n}
    (p : (graph n).Walk a b) :
    ∃ w : List Letter, a * eval w = b ∧ w.length = p.length := by
  induction p with
  | nil => exact ⟨[], by simp, rfl⟩
  | @cons a b d hab p ih =>
    obtain ⟨c, hc⟩ := ((adj_iff_letter a b).mp hab).2
    obtain ⟨w, hw, hlen⟩ := ih
    refine ⟨c :: w, ?_, by simp [hlen]⟩
    rw [eval_cons, ← mul_assoc, hc, hw]


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





theorem expandLetter_eval {n : ℕ} [NeZero n] (c : LX.Core.Letter) :
    eval (expandLetter n c) = c.eval (n := n) := by
  cases c with
  | l => simp [expandLetter, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval]
  | x => simp [expandLetter, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval]
  | r =>
    have hn : 0 < n := NeZero.pos n
    have hp := LX.Core.RotationWords.rotation_period (n := n)
    have he : LX.Core.L n ^ (n - 1) * LX.Core.L n = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hn, hp]
    have hi : LX.Core.L n ^ (n - 1) = (LX.Core.L n)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left he
    simpa [expandLetter, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval, LX.Core.R] using hi

theorem expand_eval {n : ℕ} [NeZero n] (w : List LX.Core.Letter) :
    eval (expand n w) = LX.Core.eval (n := n) w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change eval (expandLetter n c ++ expand n w) = _
    rw [eval_append, expandLetter_eval, ih, LX.Core.eval_cons]

theorem exists_word {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w = p := by
  obtain ⟨path⟩ := LX.Core.connected n hn 1 p
  obtain ⟨w, hw, _⟩ := LX.Core.word_of_walk path
  exact ⟨expand n w, by simpa [expand_eval] using hw⟩





theorem exists_shortest_word {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w = p ∧ w.length = length p := by
  obtain ⟨w, hw⟩ := exists_word hn p
  exact Nat.sInf_mem (show Set.Nonempty {k : ℕ | ∃ w : List Letter,
    eval w = p ∧ w.length = k} from ⟨w.length, w, hw, rfl⟩)





theorem length_le_diameter {n : ℕ} [NeZero n] (p : State n) :
    length p ≤ diameter n := Finset.le_sup (f := fun p : State n => length p) (Finset.mem_univ p)







end LX

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem ScanTrace.run_zero {d : Fin n → ℤ} {w : List Letter} (ht : ScanTrace d w) :
    ∀ i, run w d i = 0 := by
  induction ht with
  | done hz => exact hz
  | left _ _ _ ih => exact ih
  | swap _ _ ih => exact ih















end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]























theorem length_eq_counts (w : List Letter) : w.length = w.count .l + w.count .x := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact cost of the actual LX word: inversions plus all rotations, including orientation. -/
theorem ScanTrace.paid_length (hn : 2 ≤ n) {d : Fin n → ℤ} {w : List Letter}
    (ht : ScanTrace d w) (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d))
    (c : Fin n) : (paidWord c w).length = inversions d + paidRotations c w := by
  simp only [paidWord, List.length_append, List.length_replicate, length_eq_counts,
    ht.exchange_count hn hb hi, paidRotations]
  omega





end LX.AffineScan

end

section
namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every balanced lift's greedy price is the length of a literal word
with the specified endpoint, including its final orientation. -/
theorem greedy_lift_price_realized (hn : 2 ≤ n) (p : State n) (c : ℕ)
    (d : Fin n → ℤ) (hd : IsLift p (c : ℤ) d) (g : List Letter) (hg : ScanTrace d g) :
    eval (paidWord (c : Fin n) g)=p ∧
      (paidWord (c : Fin n) g).length=inversions d+paidRotations (c : Fin n) g := by
  have hl (i : Fin n) : labels d i=p.symm i+(c : Fin n) := by
    simpa only [labels,Int.cast_natCast] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.symm.injective (add_right_cancel hij)
  have hs := sorting_word_of_zero hn p.symm (c : Fin n) d hl g hg.run_zero
  have he : p⁻¹*eval (paidWord (c : Fin n) g)=1 := by
    simpa only [paidWord,Equiv.Perm.inv_def] using hs
  exact ⟨(inv_mul_eq_one.mp he).symm,hg.paid_length hn hd.1 hi _⟩





end LX

end

section
namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem length_lower_iff_bounded_greedy_prices (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    B ≤ length p ↔ ∀ (c : Fin n) (d : Fin n → ℤ) (g : List Letter),
      IsLift p (c : ℤ) d → (∀ i,|d i| ≤ (n : ℤ)-1) → ScanTrace d g →
        B ≤ inversions d+paidRotations c g := by
  constructor
  · intro hB c d g hd _ hg
    have hh := (length_lower_iff_greedy_prices hn p B).mp hB c.val d g hd hg
    simpa only [Fin.cast_val_eq_self] using hh
  · intro h
    obtain ⟨c,d,g,hd,hbound,hg,_,hlen⟩ := exists_shortest_bounded_greedy_word hn p
    have hb := h c d g hd hbound hg
    have hp : (paidWord c g).length=inversions d+paidRotations c g := by
      simpa only [Fin.cast_val_eq_self] using (greedy_lift_price_realized hn p c.val d hd g hg).2
    omega



end LX

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
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



/-- The even candidate is at least the conjectured diameter distance
from the identity for every even n >= 6. -/
theorem even_length_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    3*m^2-4*m+3 ≤ length (even : State n) := by
  apply (length_lower_iff_bounded_greedy_prices (by omega : 2 ≤ n) even _).mpr
  intro c d g hd _ hg
  exact even_greedy_price_lower m hm hn hd hg

theorem even_diameter_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    3*m^2-4*m+3 ≤ diameter n :=
  (even_length_lower m hm hn).trans (length_le_diameter even)

theorem even_diameter_conjecture_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    (3*(n : ℚ)^2-8*n+12)/4 ≤ (diameter n : ℚ) := by
  have hh := even_diameter_lower m hm hn
  have hq : ((3*m^2-4*m+3 : ℕ) : ℚ) ≤ (diameter n : ℚ) := by exact_mod_cast hh
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)] at hq
  push_cast at hq
  have hnq : (n : ℚ)=2*m := by exact_mod_cast hn
  rw [hnq]
  nlinarith



end LX.Antipode

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
namespace LX
variable {n : ℕ} [NeZero n]

/-- A directed potential needs a one-sided inequality for L and X only.
No inequality for the inverse cyclic shift is assumed. -/
theorem potential_word_bound (score : State n → ℕ)
    (hedge : ∀ p : State n,∀ a : Letter,score (p*eval [a]) ≤ score p+1)
    (p : State n) (w : List Letter) :
    score (p*eval w) ≤ score p+w.length := by
  induction w generalizing p with
  | nil => simp
  | cons a w ih =>
    have he : eval (n := n) (a::w)=eval [a]*eval w := by
      simpa only [List.singleton_append] using eval_append (n := n) [a] w
    rw [he,← mul_assoc]
    have htail := ih (p*eval [a])
    have hhead := hedge p a
    simp only [List.length_cons]
    omega

theorem potential_le_length (hn : 2 ≤ n) (score : State n → ℕ)
    (hzero : score 1=0)
    (hedge : ∀ p : State n,∀ a : Letter,score (p*eval [a]) ≤ score p+1)
    (p : State n) : score p ≤ length p := by
  obtain ⟨w,hw,hlen⟩ := exists_shortest_word hn p
  have hb := potential_word_bound score hedge 1 w
  simpa only [one_mul,hw,hlen,hzero,zero_add] using hb

theorem potential_le_diameter (hn : 2 ≤ n) (score : State n → ℕ)
    (hzero : score 1=0)
    (hedge : ∀ p : State n,∀ a : Letter,score (p*eval [a]) ≤ score p+1)
    (p : State n) : score p ≤ diameter n :=
  (potential_le_length hn score hzero hedge p).trans (length_le_diameter p)

/-- Checking edges on surjective permutation codes suffices to certify
the lower bound against every possible word, not just a search output. -/
theorem lower_of_code_potential (hn : 2 ≤ n) (score : State n → ℕ)
    (hzero : score 1=0)
    (checked : ∀ c : LX.Core.PermCode n,∀ a : Letter,
      score (LX.Core.decode c*eval [a]) ≤ score (LX.Core.decode c)+1)
    (p : State n) : score p ≤ diameter n := by
  apply potential_le_diameter hn score hzero ?_ p
  intro q a
  simpa only [LX.Core.decode_encode] using checked (LX.Core.encode q) a



end LX

end

section
namespace LX.Small5
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem potential_zero : score 1=0 := by decide +kernel

theorem potential_edges : ∀ c : LX.Core.PermCode 5,∀ a : Letter,
    score (LX.Core.decode c*eval [a]) ≤ score (LX.Core.decode c)+1 := by
  have checked : ∀ c : LX.Core.PermCode 5,
      score (LX.Core.decode c*eval [.l]) ≤ score (LX.Core.decode c)+1 ∧
      score (LX.Core.decode c*eval [.x]) ≤ score (LX.Core.decode c)+1 := by
    decide +kernel
  intro c a
  cases a with
  | l => exact (checked c).1
  | x => exact (checked c).2



theorem farthest_score : score farthest=11 := by decide +kernel

theorem diameter_lower : 11 ≤ diameter 5 := by
  have hb := lower_of_code_potential (by decide : 2 ≤ 5) score
    potential_zero potential_edges farthest
  simpa only [farthest_score] using hb



end LX.Small5

end

section
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem odd_length_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) :
    3*m^2-m+1 ≤ length (odd m (by omega) hn) := by
  apply (length_lower_iff_bounded_greedy_prices (by omega : 2 ≤ n) (odd m (by omega) hn) _).mpr
  intro c d g hd _ hg
  exact odd_greedy_price_lower m hm hn hd hg

/-- Sharp odd lower bound for all odd n >= 5, including the independently
checked five-position base case. -/
theorem odd_diameter_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    3*m^2-m+1 ≤ diameter n := by
  by_cases hm2 : m=2
  · subst m
    have hn5 : n=5 := by omega
    subst n
    change 11 ≤ diameter 5
    exact LX.Small5.diameter_lower
  · exact (odd_length_lower m (by omega) hn).trans (length_le_diameter (odd m (by omega) hn))

theorem odd_diameter_conjecture_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    (3*(n : ℚ)^2-8*n+9)/4 ≤ (diameter n : ℚ) := by
  have hh := odd_diameter_lower m hm hn
  have hq : ((3*m^2-m+1 : ℕ) : ℚ) ≤ (diameter n : ℚ) := by exact_mod_cast hh
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : m ≤ 3*m^2)] at hq
  push_cast at hq
  have hnq : (n : ℚ)=2*m+1 := by exact_mod_cast hn
  rw [hnq]
  nlinarith



end LX.Antipode

end

namespace LX
end LX
open LX

/-- The conjectured value is a lower bound for every n > 4. The parity
term gives constant 3 in even size and 9/4 in odd size. -/
theorem solution (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    (3*(n : ℚ)^2-8*n+12-3*((n%2 : ℕ) : ℚ))/4 ≤ (diameter n : ℚ) := by
  have he : n%2=0 ∨ n%2=1 := by omega
  rcases he with he | he
  · rw [he,Nat.cast_zero,mul_zero,sub_zero]
    exact Antipode.even_diameter_conjecture_lower (n/2) (by omega) (by omega)
  · rw [he,Nat.cast_one,mul_one]
    have hh := Antipode.odd_diameter_conjecture_lower (n/2) (by omega) (by omega : n=2*(n/2)+1)
    convert hh using 1 <;> ring
