-- Prove2me | solution 1 for LX.AffineScan.ScanTrace.paid_length_le_any_word
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:47:59.950111+00:00
-- url     : https://prove2.me/submissions/e29c290b-a13e-4139-8651-d4d655c7f259

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
import Definitions.Def_LX_AffineDeletion
import Definitions.Def_LX_AffineRankOrder
import Definitions.Def_LX_AffineScan
import Definitions.Def_LX_BufferProgram
import Definitions.Def_LX_EventTrace
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyRotationOptimality
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionIndices
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PairEvents
import Definitions.Def_LX_PairOrder
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SweepCarrier
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AffineScan_ScanTrace_exchange_count
import Theorems.Thm_LX_AffineScan_ScanTrace_rotations_le_of_compare_zero
import Theorems.Thm_LX_AffineScan_saturated_sweep_rank_le_run
import Theorems.Thm_LX_AffineScan_zero_of_rank_le_zero
import Theorems.Thm_LX_Core_LiftedModel_affine_pair_reduction
import Theorems.Thm_LX_Core_LiftedModel_before_run_of_absent
import Theorems.Thm_LX_Core_LiftedModel_card_inversion_indices
import Theorems.Thm_LX_Core_LiftedModel_mem_events
import Theorems.Thm_LX_Core_LiftedModel_step_aligned
import Theorems.Thm_LX_Core_LiftedModel_x_as_pair_rename
import Theorems.Thm_LX_Core_LiftedModel_x_changes_only_event
import Theorems.Thm_LX_Core_PhysicalModel_visible_step
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

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h




















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











theorem visible_run (w : List Letter) (s : Configuration n) :
    visible (run w s) = visible s * eval w := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => rw [run, ih, visible_step, eval_cons, mul_assoc]



@[simp] theorem visible_initial : visible (initial (n := n)) = 1 := by
  simp [visible, initial]


end LX.Core.PhysicalModel

end

section
/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]







theorem neighboring_positions_distinct (hn : 2 ≤ n) (c : Fin n) : c ≠ c + 1 := by
  have h1 : (1 : Fin n) ≠ 0 := by
    intro h
    have := Fin.one_eq_zero_iff.mp h
    omega
  intro h
  have h' : c + 0 = c + 1 := by simpa using h
  exact h1 (add_left_cancel h').symm









theorem run_physical (w : List Letter) (s : Configuration n) :
    (run w s).physical = PhysicalModel.run w s.physical := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih (step a s)

theorem run_aligned (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) : Aligned (run w s) := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih => exact ih (step_aligned hn a hs)



theorem cursor_run (w : List Letter) (s : Configuration n) :
    (run w s).cursor = s.cursor + (w.map increment).sum := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => simp [run, ih, step, add_assoc]



theorem initial_aligned : Aligned (initial (n := n)) := by
  constructor
  · rfl
  · intro i
    simp [initial, PhysicalModel.initial]
    rfl




theorem cast_eq_iff_modEq (a b : ℤ) :
    (a : Fin n) = (b : Fin n) ↔ Int.ModEq (n : ℤ) a b := by
  constructor
  · intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_intCast] at hh
    have hi := congrArg (fun k : ℕ => (k : ℤ)) hh
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hn0),
      Int.toNat_of_nonneg (Int.emod_nonneg b hn0)] at hi
    exact hi
  · exact AffineLift.cast_eq_of_modEq




end LX.Core.LiftedModel

end

section
/-! A lifted pair is a pair of finite labels together with an integer relative
copy offset. Equal pair events implement the same periodic involution. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]












omit [NeZero n] in
theorem pair_rename_reverse (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    pairRename b a (-shift)=pairRename a b shift := by
  have ho : pairOffset b a (-shift)=pairOffset a b shift := by
    funext i
    by_cases ha : i=a
    · subst i; simp [pairOffset, hab]
    · by_cases hb : i=b
      · subst i; simp [pairOffset, Ne.symm hab]
      · simp [pairOffset, ha, hb]
  simp only [pairRename, Equiv.swap_comm b a, ho]

/-- Alignment forces the offset to be a whole number of turns. No quotient is
rounded or silently discarded in the pair-renaming representation. -/
theorem pair_offset_dvd {s : Configuration n} (hs : Aligned s)
    (a b : Fin n) (ha : s.physical.tokens s.physical.cursor=a)
    (hb : s.physical.tokens (s.physical.cursor+1)=b) :
    (n : ℤ) ∣ s.position a+1-s.position b := by
  have hcast : ((s.position a+1 : ℤ) : Fin n)=(s.position b : Fin n) := by
    rw [Int.cast_add, hs.2 a, hs.2 b, ← ha, ← hb]
    simp
  have hm := (cast_eq_iff_modEq _ _).mp hcast
  have hh := hm.sub_right (s.position b)
  apply Int.modEq_zero_iff_dvd.mp
  simpa only [sub_self] using hh



end LX.Core.LiftedModel

end

section
/-! Canonical keys of lifted pair events. The stored shift is n times the copy
index, avoiding any loss through integer division. Order reversal negates it. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]







omit [NeZero n] in
theorem normalize_pair_action (a b : Fin n) (shift : ℤ) (hab : a ≠ b) :
    (normalizePair a b shift).action=pairRename a b shift := by
  unfold normalizePair
  split_ifs
  · rfl
  · exact pair_rename_reverse a b shift hab





theorem x_event_action (hn : 2 ≤ n) (s : Configuration n) :
    step .x s=(eventKey s).action s := by
  have hne : s.physical.tokens s.physical.cursor ≠ s.physical.tokens (s.physical.cursor+1) := by
    intro h
    exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  rw [eventKey, normalize_pair_action _ _ _ hne]
  exact x_as_pair_rename s _ _ hne rfl rfl

theorem event_shift_dvd {s : Configuration n} (hs : Aligned s) :
    (n : ℤ) ∣ (eventKey s).shift := by
  have h := pair_offset_dvd hs _ _ rfl rfl
  dsimp only [eventKey, normalizePair]
  split_ifs
  · exact h
  · exact dvd_neg.mpr h







end LX.Core.LiftedModel

end

section
/-! Repeated lifted pairs can be eliminated from every finite LX.Core word. The
integer endpoint configuration and the entire L/R subsequence are preserved.
Identifying the remaining number of X with affine inversion length is separate. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]







theorem event_count_length (w : List Letter) (s : Configuration n) :
    (events w s).length=BufferProgram.exchanges w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => cases a <;> simp [events, BufferProgram.exchanges, ih]

theorem length_eq_event_rotation (w : List Letter) (s : Configuration n) :
    w.length=(events w s).length+BufferProgram.rotations w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    have h := ih (step a s)
    cases a <;> simp_all [events, BufferProgram.rotations] <;> omega

/-- The reduced word has the same paid rotation sequence and the same exact
lifted endpoint as the original word. The trace has no repeated lifted pair. -/
theorem affine_reduced_word (hn : 2 ≤ n) (w : List Letter) :
    ∃ v : List Letter,
      run v (initial (n := n))=run w (initial (n := n)) ∧
      eval v=eval (n := n) w ∧
      rotationLetters v=rotationLetters w ∧
      BufferProgram.rotations v=BufferProgram.rotations w ∧
      (events v (initial (n := n))).Nodup ∧ v.length ≤ w.length ∧ v.Sublist w := by
  obtain ⟨v, he, hr, hnd, hlen, hsub⟩ := affine_pair_reduction hn w (initial (n := n))
  refine ⟨v, he, ?_, hr, ?_, hnd, hlen, hsub⟩
  · have h := congrArg (fun s : Configuration n => PhysicalModel.visible s.physical) he
    simpa only [run_physical, PhysicalModel.visible_run, initial,
      PhysicalModel.visible_initial, one_mul] using h
  · exact congrArg List.length hr



end LX.Core.LiftedModel

end

section
/-! Relative order of periodic token copies. A physical X changes the order of
exactly its own lifted pair orbit. This links reduced traces to inversions. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem positions_ne_periodic {s : Configuration n} (hs : Aligned s)
    (a b : Fin n) (hab : a ≠ b) (shift : ℤ) (hdiv : (n : ℤ) ∣ shift) :
    s.position a ≠ s.position b+shift := by
  intro he
  have hz : (shift : Fin n)=0 := by
    have h := AffineLift.cast_eq_of_modEq (Int.modEq_zero_iff_dvd.mpr hdiv)
    simpa using h
  have hc : (s.position a : Fin n)=(s.position b : Fin n) := by
    rw [he, Int.cast_add, hz, add_zero]
  rw [hs.2 a, hs.2 b] at hc
  exact hab (s.physical.tokens.symm.injective hc)

omit [NeZero n] in
theorem pair_action_order {key : PairKey n} {s : Configuration n}
    (hne : key.first ≠ key.second)
    (hpos : s.position key.first ≠ s.position key.second+key.shift) :
    key.Before (key.action s) ↔ ¬ key.Before s := by
  simp only [PairKey.Before, PairKey.action, pairRename, rename,
    Equiv.swap_apply_left, Equiv.swap_apply_right, pairOffset,
    ite_true, ite_eq_right (Ne.symm hne)]
  omega



theorem x_changes_event (hn : 2 ≤ n) {s : Configuration n} (hs : Aligned s)
    (key : PairKey n) (hk : key.Valid) (he : eventKey s=key) :
    key.Before (step .x s) ↔ ¬ key.Before s := by
  rw [x_event_action hn s, he]
  exact pair_action_order (ne_of_lt hk.1)
    (positions_ne_periodic hs key.first key.second (ne_of_lt hk.1) key.shift hk.2)

theorem event_key_valid (hn : 2 ≤ n) {s : Configuration n} (hs : Aligned s) :
    (eventKey s).Valid := by
  refine ⟨?_, event_shift_dvd hs⟩
  have hne : s.physical.tokens s.physical.cursor ≠ s.physical.tokens (s.physical.cursor+1) := by
    intro h
    exact neighboring_positions_distinct hn _ (s.physical.tokens.injective h)
  dsimp only [eventKey, normalizePair]
  split_ifs with h
  · exact lt_of_le_of_ne h hne
  · exact lt_of_not_ge h



end LX.Core.LiftedModel

end

section
/-! Finite copy-index intervals for the inversions of one periodic pair. -/
noncomputable section

namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]



omit [NeZero n] in
theorem mem_inversion_indices (q k : ℤ) :
    k ∈ inversionIndices q ↔ ¬ ((0 ≤ k) ↔ (-q ≤ k)) := by
  unfold inversionIndices
  split_ifs <;> simp only [Finset.mem_Ico] <;> omega



omit [NeZero n] in
theorem periodic_order_quotient {N : ℤ} (hN : 0 < N) (a b k : ℤ)
    (hr : (b-a)%N ≠ 0) :
    a < b+N*k ↔ -( (b-a)/N ) ≤ k := by
  have hdiv := Int.ediv_mul_add_emod (b-a) N
  have hr0 := Int.emod_nonneg (b-a) (ne_of_gt hN)
  have hr1 := Int.emod_lt_of_pos (b-a) hN
  have hrpos : 1 ≤ (b-a)%N := by omega
  constructor
  · intro h
    by_contra hbad
    have hk : (b-a)/N+k ≤ -1 := by omega
    nlinarith
  · intro h
    have hk : 0 ≤ (b-a)/N+k := by omega
    nlinarith

theorem position_difference_mod_ne {s : Configuration n} (hs : Aligned s)
    (i j : Fin n) (hij : i ≠ j) : (s.position j-s.position i)%(n : ℤ) ≠ 0 := by
  intro hzero
  have hdiv := Int.ediv_mul_add_emod (s.position j-s.position i) (n : ℤ)
  rw [hzero, add_zero] at hdiv
  apply positions_ne_periodic hs i j hij (-(n : ℤ)*((s.position j-s.position i)/(n : ℤ)))
  · exact dvd_mul_of_dvd_left (dvd_neg.mpr (dvd_refl _)) _
  · nlinarith

theorem initial_pair_order (i j : Fin n) (hij : i < j) (k : ℤ) :
    (i : ℤ) < (j : ℤ)+(n : ℤ)*k ↔ 0 ≤ k := by
  have hi0 : (0 : ℤ) ≤ i := by positivity
  have hj0 : (0 : ℤ) ≤ j := by positivity
  have hin : (i : ℤ) < n := by exact_mod_cast i.isLt
  have hjn : (j : ℤ) < n := by exact_mod_cast j.isLt
  have hlt : (i : ℤ) < j := by exact_mod_cast hij
  constructor
  · intro h
    by_contra hbad
    have hk : k ≤ -1 := by omega
    nlinarith
  · intro h
    have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    nlinarith

theorem inversion_index_order {s : Configuration n} (hs : Aligned s)
    (i j : Fin n) (hij : i < j) (k : ℤ) :
    k ∈ inversionIndices ((s.position j-s.position i)/(n : ℤ)) ↔
      ¬ (((i : ℤ) < (j : ℤ)+(n : ℤ)*k) ↔
        s.position i < s.position j+(n : ℤ)*k) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [initial_pair_order i j hij, periodic_order_quotient hn _ _ k
    (position_difference_mod_ne hs i j (ne_of_lt hij)), mem_inversion_indices]



end LX.Core.LiftedModel

end
end

section
/-! A trace without repeated lifted pairs consists precisely of the pair orbits
whose relative order differs between the initial and final configurations. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]



theorem before_run_of_present (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (key : PairKey n) (hk : key.Valid)
    (hnd : (events w s).Nodup) (hmem : key ∈ events w s) :
    key.Before (run w s) ↔ ¬ key.Before s := by
  induction w generalizing s with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons a w ih =>
    have hsa := step_aligned hn a hs
    cases a with
    | l =>
      have h := ih hsa hnd hmem
      simpa only [run, PairKey.Before, step] using h
    | r =>
      have h := ih hsa hnd hmem
      simpa only [run, PairKey.Before, step] using h
    | x =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hmem with he | hm
      · have ha : key ∉ events w (step .x s) := by simpa only [he] using hnot
        exact (before_run_of_absent hn w hsa key hk ha).trans (x_changes_event hn hs key hk he.symm)
      · have hne : eventKey s ≠ key := fun he => hnot (he ▸ hm)
        exact (ih hsa htail hm).trans (not_congr (x_changes_only_event hn hs key hk hne))

theorem event_member_valid (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (key : PairKey n) (hmem : key ∈ events w s) : key.Valid := by
  obtain ⟨u, v, _, hk⟩ := (mem_events w s key).mp hmem
  rw [← hk]
  exact event_key_valid hn (run_aligned hn u hs)

theorem reduced_trace_inversions (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) (hnd : (events w s).Nodup) (key : PairKey n) :
    key ∈ events w s ↔ key.Valid ∧ ¬ (key.Before s ↔ key.Before (run w s)) := by
  constructor
  · intro hmem
    have hk := event_member_valid hn w hs key hmem
    refine ⟨hk, ?_⟩
    have h := before_run_of_present hn w hs key hk hnd hmem
    tauto
  · rintro ⟨hk, hchange⟩
    by_contra hno
    exact hchange (before_run_of_absent hn w hs key hk hno).symm



end LX.Core.LiftedModel

end

section
/-! A finite set of all affine inversions, with its explicit double-sum cardinality. -/
noncomputable section

namespace LX.Core.LiftedModel
open scoped BigOperators
variable {n : ℕ} [NeZero n]







theorem mk_mem_inversionPairs (F : Fin n → ℤ) (i j : Fin n) (k : ℤ) :
    (⟨i,j,(n : ℤ)*k⟩ : PairKey n) ∈ inversionPairs F ↔
      i < j ∧ k ∈ inversionIndices ((F j-F i)/(n : ℤ)) := by
  change pairIndexEmbedding ⟨i,j,k⟩ ∈ Finset.map pairIndexEmbedding _ ↔ _
  rw [Finset.mem_map']
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
  by_cases hij : i < j <;> simp [hij]

theorem inversionPairs_card (F : Fin n → ℤ) :
    (inversionPairs F).card=inversionCount F := by
  unfold inversionPairs inversionCount
  rw [Finset.card_map, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [card_inversion_indices]

theorem inversionPairs_valid (F : Fin n → ℤ) (key : PairKey n)
    (hk : key ∈ inversionPairs F) : key.Valid := by
  obtain ⟨⟨i,j,k⟩, _, hkey⟩ := Finset.mem_map.mp hk
  change (⟨i,j,(n : ℤ)*k⟩ : PairKey n)=key at hkey
  subst key
  have hmem := (mk_mem_inversionPairs F i j k).mp hk
  exact ⟨hmem.1, dvd_mul_right _ _⟩

theorem mem_inversionPairs_iff {s : Configuration n} (hs : Aligned s) (key : PairKey n) :
    key ∈ inversionPairs s.position ↔
      key.Valid ∧ ¬ (key.Before (initial (n := n)) ↔ key.Before s) := by
  constructor
  · intro hm
    have hk := inversionPairs_valid s.position key hm
    obtain ⟨k, hshift⟩ := hk.2
    cases key with
    | mk i j shift =>
      change shift=(n : ℤ)*k at hshift
      subst shift
      have hmem := (mk_mem_inversionPairs s.position i j k).mp hm
      exact ⟨hk, (inversion_index_order hs i j hmem.1 k).mp hmem.2⟩
  · rintro ⟨hk, hchange⟩
    obtain ⟨k, hshift⟩ := hk.2
    cases key with
    | mk i j shift =>
      change shift=(n : ℤ)*k at hshift
      subst shift
      apply (mk_mem_inversionPairs s.position i j k).mpr
      exact ⟨hk.1, (inversion_index_order hs i j hk.1 k).mpr hchange⟩

/-- In a reduced trace, the number of X is exactly the explicit affine inversion
sum of the final integer positions. -/
theorem reduced_exchange_count (hn : 2 ≤ n) (w : List Letter)
    (hnd : (events w (initial (n := n))).Nodup) :
    BufferProgram.exchanges w=inversionCount (run w (initial (n := n))).position := by
  have hs := run_aligned hn w (initial_aligned (n := n))
  have hset : (events w (initial (n := n))).toFinset=
      inversionPairs (run w (initial (n := n))).position := by
    ext key
    rw [List.mem_toFinset, reduced_trace_inversions hn w (initial_aligned (n := n)) hnd,
      mem_inversionPairs_iff hs]
  have hcard := congrArg Finset.card hset
  rw [List.toFinset_card_of_nodup hnd, event_count_length, inversionPairs_card] at hcard
  exact hcard



end LX.Core.LiftedModel

end
end

section
/-! Exact paid length after affine pair deletion, and its application to the
service of all cycles reachable from the chosen root. -/
namespace LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]

/-- Full affine deletion theorem: preserve the entire lifted endpoint and every
L/R letter, with exactly the affine inversion count remaining as X. -/
theorem affine_reduction_exact (hn : 2 ≤ n) (w : List Letter) :
    ∃ v : List Letter,
      run v (initial (n := n))=run w (initial (n := n)) ∧
      eval v=eval (n := n) w ∧
      rotationLetters v=rotationLetters w ∧
      BufferProgram.exchanges v=inversionCount (run w (initial (n := n))).position ∧
      v.length=inversionCount (run w (initial (n := n))).position+BufferProgram.rotations w ∧
      v.Sublist w := by
  obtain ⟨v, he, hv, hr, hrot, hnd, _, hsub⟩ := affine_reduced_word hn w
  have hx := reduced_exchange_count hn v hnd
  rw [he] at hx
  refine ⟨v, he, hv, hr, hx, ?_, hsub⟩
  rw [length_eq_event_rotation v (initial (n := n)), event_count_length, hx, hrot]


end LX.Core.LiftedModel

namespace LX.Core.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]


end LX.Core.BufferProgram

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
/-! Local invariants for the forward scan used to construct LX words.
This module proves progress and energy descent, not the quadratic price. -/
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]















omit [NeZero n] in
theorem rotate_sum (d : Fin n → ℤ) : ∑ i, rotate d i = ∑ i, d i :=
  Equiv.sum_comp (finRotate n) d


theorem exchange_sum (d : Fin n → ℤ) : ∑ i, exchange d i = ∑ i, d i := by
  simp [exchange, Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp]















theorem run_append (u v : List Letter) (d : Fin n → ℤ) :
    run (u ++ v) d = run v (run u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons a u ih => exact ih (step a d)

theorem run_sum (w : List Letter) (d : Fin n → ℤ) : ∑ i, run w d i = ∑ i, d i := by
  induction w generalizing d with
  | nil => rfl
  | cons a w ih =>
    rw [run, ih]
    cases a with
    | l => exact rotate_sum d
    | x => exact exchange_sum d

















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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]













theorem run_sweep_step (d : Fin n → ℤ) : run (sweepStepWord d) d = sweepStep d := by
  unfold sweepStepWord sweepStep compareHead
  split_ifs <;> rfl

theorem run_sweep_word (d : Fin n → ℤ) (k : ℕ) : run (sweepWord d k) d = sweep d k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sweepWord, run_append, ih, run_sweep_step, sweep]


























end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem sweep_balance (d : Fin n → ℤ) (k : ℕ) :
    ∑ i, sweep d k i = ∑ i, d i := by
  rw [← run_sweep_word, run_sum]






























end LX.AffineScan

end

section
namespace LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]











theorem cursor_eq_left_count (w : List Letter) :
    (run (w.map Letter.toCore) (initial (n := n))).cursor=(w.count .l : ℤ) := by
  rw [cursor_run]
  simp only [initial,zero_add,List.map_map]
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [Letter.toCore,increment,ih,add_comm]

theorem rotations_eq_left_count (w : List Letter) :
    LX.Core.BufferProgram.rotations (w.map Letter.toCore)=w.count .l := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | l => simpa [LX.Core.BufferProgram.rotations,Letter.toCore] using congrArg Nat.succ ih
    | x => simpa [LX.Core.BufferProgram.rotations,Letter.toCore] using ih

/-- Swap cancellation preserves the endpoint and all paid rotations;
therefore its exact inversion price is a lower bound for every LX word. -/
theorem word_inversion_cursor_lower (hn : 2 ≤ n) (w : List Letter) :
    (inversionCount (run (w.map Letter.toCore) (initial (n := n))).position : ℤ)+
      (run (w.map Letter.toCore) (initial (n := n))).cursor ≤ (w.length : ℤ) := by
  obtain ⟨v,_,_,_,_,hlen,hsub⟩ := affine_reduction_exact hn (w.map Letter.toCore)
  have hb := hsub.length_le
  rw [hlen,rotations_eq_left_count,List.length_map] at hb
  rw [cursor_eq_left_count]
  exact_mod_cast hb





end LX.DirectedTokenLower

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem saturated_sweep_balance (d : Fin n → ℤ) (t : ℕ) :
    (∑ i,saturatedSweep d t i)=∑ i,d i := by
  unfold saturatedSweep compareHead
  split_ifs
  · rw [exchange_sum,sweep_balance]
  · rw [sweep_balance]



theorem saturated_sweep_zero_of_word (hn : 2 ≤ n) (d : Fin n → ℤ) (w : List Letter)
    (hb : ∑ i,d i=0) (hz : ∀ i,run w d i=0) :
    ∀ i,saturatedSweep d (w.count .l) i=0 := by
  have hr := saturated_sweep_rank_le_run hn d w
  have he : run w d=(fun _ => 0) := funext hz
  rw [he] at hr
  exact zero_of_rank_le_zero _ (by rw [saturated_sweep_balance,hb]) hr

/-- Optimality of the greedy scan's rotation count for a fixed exact lift.
The final phase and the exchange count still need to be charged separately. -/
theorem ScanTrace.rotations_le_any_word (hn : 2 ≤ n) {d : Fin n → ℤ}
    {g : List Letter} (hg : ScanTrace d g) (hb : ∑ i,d i=0)
    (w : List Letter) (hw : ∀ i,run w d i=0) : g.count .l ≤ w.count .l :=
  hg.rotations_le_of_compare_zero hn _ (saturated_sweep_zero_of_word hn d w hb hw)



end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Greedy scheduling plus the exact final rotation is no longer than
any word reaching the same lifted endpoint and cursor residue. -/
theorem solution (hn : 2 ≤ n) {d : Fin n → ℤ}
    {g : List Letter} (hg : ScanTrace d g) (hb : ∑ i,d i=0)
    (hi : Function.Injective (labels d)) (w : List Letter) (hw : ∀ i,run w d i=0) :
    (paidWord (w.count .l : Fin n) g).length ≤ w.length := by
  have hrot := hg.rotations_le_any_word hn hb w hw
  have hcost := DirectedTokenLower.word_inversion_cursor_lower hn w
  have hpos := funext (LiftedScan.exact_positions_of_zero hn d w hw)
  rw [hpos,DirectedTokenLower.cursor_eq_left_count] at hcost
  change (inversions d : ℤ)+(w.count .l : ℤ) ≤ (w.length : ℤ) at hcost
  have hcost' : inversions d+w.count .l ≤ w.length := by exact_mod_cast hcost
  have hpad : ((w.count .l : Fin n)-(g.count .l : Fin n)).val ≤ w.count .l-g.count .l := by
    rw [← Nat.cast_sub hrot,Fin.val_natCast]
    exact Nat.mod_le _ _
  rw [hg.paid_length hn hb hi]
  unfold paidRotations
  omega
