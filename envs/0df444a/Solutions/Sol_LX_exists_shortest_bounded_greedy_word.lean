-- Prove2me | solution 1 for LX.exists_shortest_bounded_greedy_word
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:55:39.950189+00:00
-- url     : https://prove2.me/submissions/c6836cb5-af2e-43ce-a781-a4e5f39c117b

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
import Definitions.Def_LX_Connected
import Definitions.Def_LX_FinitePairReduction
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedScanBridge
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_ScanTrace_exchange_count
import Theorems.Thm_LX_AffineScan_ScanTrace_paid_length_le_any_word
import Theorems.Thm_LX_AffineScan_exists_exact_word_board
import Theorems.Thm_LX_AffineScan_exists_scan_trace
import Theorems.Thm_LX_AffineScan_sorting_word_of_zero
import Theorems.Thm_LX_FinitePairReduction_delete_returning_pair
import Theorems.Thm_LX_FinitePairReduction_mem_partners
import Theorems.Thm_LX_FinitePairReduction_position_run_partner_bound
import Theorems.Thm_LX_LiftedScan_exact_positions_of_zero

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.DirectedTokenLower
end LX.DirectedTokenLower
namespace LX.FinitePairReduction
end LX.FinitePairReduction
namespace LX.ForwardCarrier
end LX.ForwardCarrier
namespace LX.LiftedScan
end LX.LiftedScan
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

theorem Letter.eval_mem {n : ℕ} [NeZero n] (a : Letter) :
    a.eval (n := n) ∈ generators n := by
  cases a <;> simp [Letter.eval, generators]




end LX.Core

end

section
/-! Integer residues and normalization of the phase of a balanced lift.
The normalized phase is represented by an element of `Fin n`. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast

variable {n : ℕ} [NeZero n]

theorem modulus_pos : (0 : ℤ) < n := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

theorem residue_val (z : ℤ) : ((Fin.intCast z : Fin n) : ℤ) = z % (n : ℤ) := by
  change ((z : Fin n).val : ℤ) = _
  rw [Fin.val_intCast]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt modulus_pos))

theorem modEq_residue (z : ℤ) :
    Int.ModEq (n : ℤ) z ((Fin.intCast z : Fin n) : ℤ) := by
  rw [residue_val]
  simp [Int.ModEq]

theorem normalize_phase {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : IsLift p ((Fin.intCast c : Fin n) : ℤ) d := by
  refine ⟨hd.1, ?_⟩
  intro i
  exact (hd.2 i).trans ((modEq_residue c).add_left (p.symm i : ℤ))


end LX.Core.AffineLift

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



theorem length_le_word {n : ℕ} [NeZero n] (w : List Letter) :
    length (eval (n := n) w) ≤ w.length := by
  exact Nat.sInf_le ⟨w, rfl, rfl⟩

theorem exists_shortest_word {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    ∃ w : List Letter, eval w = p ∧ w.length = length p := by
  obtain ⟨w, hw⟩ := exists_word hn p
  exact Nat.sInf_mem (show Set.Nonempty {k : ℕ | ∃ w : List Letter,
    eval w = p ∧ w.length = k} from ⟨w.length, w, hw, rfl⟩)













end LX

end

section
namespace LX.FinitePairReduction
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]









theorem eval_cons_action (a : Letter) (w : List Letter) :
    eval (n := n) (a::w)=a.toCore.eval*eval w :=
  LX.Core.eval_cons a.toCore (w.map Letter.toCore)







theorem shortest_tail (p : State n) (a : Letter) (w : List Letter)
    (h : ShortestFrom p (a::w)) : ShortestFrom (p*eval [a]) w := by
  intro v hv
  have hh := h (a::v) (by simpa only [eval_cons_action,eval_nil,mul_one,mul_assoc] using hv)
  simpa only [List.length_cons,Nat.add_le_add_iff_right] using hh



theorem shortest_no_partner_return (p : State n) (i j : Fin n) (w : List Letter)
    (hmin : ShortestFrom p (.x::w)) (hhead : HeadPair p i j) :
    j ∉ partners i w (p*eval [.x]) := by
  intro hmem
  obtain ⟨u,v,he,hsecond⟩ := mem_partners i j w (p*eval [.x]) hmem
  have hend := delete_returning_pair p i j u v hhead hsecond
  have hshort := hmin (u++v) (by simpa only [he] using hend.symm)
  simp only [he,List.length_cons,List.length_append] at hshort
  omega

theorem shortest_partners_nodup (i : Fin n) (w : List Letter) (p : State n)
    (hmin : ShortestFrom p w) : (partners i w p).Nodup := by
  induction w generalizing p with
  | nil => simp [partners]
  | cons a w ih =>
    have ht := ih (p*eval [a]) (shortest_tail p a w hmin)
    cases a with
    | l => exact ht
    | x =>
      by_cases h0 : p 0=i
      · have hn := shortest_no_partner_return p i (p 1) w hmin (Or.inl ⟨h0,rfl⟩)
        simpa only [partners,headPartners,ite_eq_left h0,List.singleton_append,List.nodup_cons] using And.intro hn ht
      · by_cases h1 : p 1=i
        · have hn := shortest_no_partner_return p i (p 0) w hmin (Or.inr ⟨rfl,h1⟩)
          simpa only [partners,headPartners,ite_eq_right h0,ite_eq_left h1,List.singleton_append,List.nodup_cons] using And.intro hn ht
        · simpa only [partners,headPartners,ite_eq_right h0,ite_eq_right h1,List.nil_append] using ht

theorem partner_ne_self (hn : 2 ≤ n) (i j : Fin n) (w : List Letter) (p : State n)
    (hj : j ∈ partners i w p) : j ≠ i := by
  obtain ⟨u,_,_,hp⟩ := mem_partners i j w p hj
  have h01 : (0 : Fin n) ≠ 1 := by intro h; have := Fin.one_eq_zero_iff.mp h.symm; omega
  let q : State n := p*eval u
  have hne : q 0 ≠ q 1 := fun h => h01 (q.injective h)
  change HeadPair q i j at hp
  rcases hp with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact fun he => hne (h0.trans (h1.trans he).symm)
  · exact fun he => hne ((h0.trans he).trans h1.symm)

theorem shortest_partner_count (hn : 2 ≤ n) (i : Fin n) (w : List Letter) (p : State n)
    (hmin : ShortestFrom p w) : (partners i w p).length ≤ n-1 := by
  have hnd := shortest_partners_nodup i w p hmin
  have hself : i ∉ partners i w p := fun h => partner_ne_self hn i i w p h rfl
  have hc := (List.nodup_cons.mpr ⟨hself,hnd⟩).length_le_card
  simp only [List.length_cons,Fintype.card_fin] at hc
  omega

theorem shortest_from_of_length (p : State n) (w : List Letter)
    (hw : w.length=length (eval (n := n) w)) : ShortestFrom p w := by
  intro v hv
  have he : eval (n := n) v=eval w := mul_left_cancel hv
  have hh := length_le_word (n := n) v
  rw [he,← hw] at hh
  exact hh



end LX.FinitePairReduction

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
namespace LX.FinitePairReduction
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]





/-- Every shortest directed word moves each named token by fewer than n
integer positions, because its exchange partners cannot repeat. -/
theorem shortest_displacement_bound (hn : 2 ≤ n) (w : List Letter)
    (hw : w.length=length (eval (n := n) w)) (i : Fin n) :
    |(run (w.map Letter.toCore) (initial (n := n))).position i-(i : ℤ)| ≤ (n : ℤ)-1 := by
  have hc := shortest_partner_count hn i w 1 (shortest_from_of_length 1 w hw)
  have hb := position_run_partner_bound w (initial (n := n)) i
  simp only [initial,LiftedScan.visible,LX.Core.PhysicalModel.visible_initial] at hb
  have hci : ((partners i w 1).length : ℤ) ≤ (n : ℤ)-1 := by omega
  exact hb.trans hci



end LX.FinitePairReduction

end

namespace LX
end LX
open LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- A shortest greedy representative exists with finite phase and all
integer displacements strictly between -n and n. The bound comes from
deleting repeated finite label pairs, not an energy-minimality assumption. -/
theorem solution (hn : 2 ≤ n) (p : State n) :
    ∃ c : Fin n,∃ d : Fin n → ℤ,∃ g : List Letter,
      IsLift p (c : ℤ) d ∧ (∀ i,|d i| ≤ (n : ℤ)-1) ∧ ScanTrace d g ∧
      eval (paidWord c g)=p ∧ (paidWord c g).length=length p := by
  obtain ⟨w,hw,hlen⟩ := exists_shortest_word hn p
  obtain ⟨d,hd,hzero⟩ := exists_exact_word_board hn w
  have hpos := LiftedScan.exact_positions_of_zero hn d w hzero
  have hbound (i : Fin n) : |d i| ≤ (n : ℤ)-1 := by
    have hh := FinitePairReduction.shortest_displacement_bound hn w (by rw [hw]; exact hlen) i
    rw [hpos i,add_sub_cancel_left] at hh
    exact hh
  rw [hw] at hd
  let c : Fin n := (w.count .l : Fin n)
  have hdc : IsLift p (c : ℤ) d := by
    have hh := normalize_phase hd
    change IsLift p (((w.count .l : ℤ) : Fin n) : ℤ) d at hh
    simpa only [c,Int.cast_natCast] using hh
  have hl (i : Fin n) : labels d i=p.symm i+(c : Fin n) := by
    simpa only [labels,Int.cast_natCast,Fin.cast_val_eq_self] using lift_residue hdc i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.symm.injective (add_right_cancel hij)
  obtain ⟨g,hg⟩ := exists_scan_trace hn d hd.1 hi
  have he : eval (paidWord c g)=p := by
    simpa only [Fin.cast_val_eq_self] using (greedy_lift_price_realized hn p c.val d hdc g hg).1
  have hupper : (paidWord c g).length ≤ w.length :=
    hg.paid_length_le_any_word hn hd.1 hi w hzero
  have hlower := length_le_word (n := n) (paidWord c g)
  rw [he] at hlower
  refine ⟨c,?_⟩
  refine ⟨d,?_⟩
  refine ⟨g,hdc,hbound,hg,he,?_⟩
  exact Nat.le_antisymm (hupper.trans_eq hlen) hlower
