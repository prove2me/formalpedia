-- Prove2me | solution 1 for LX.Core.ZeroGap.SortingTrace.events
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:40:01.778899+00:00
-- url     : https://prove2.me/submissions/6e9151de-4009-4175-bb3a-56fe0cb41bca

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PortRoute
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventTravel
import Definitions.Def_LX_ZeroGapExchange
import Definitions.Def_LX_ZeroGapPair
import Definitions.Def_LX_ZeroGapSorting
import Theorems.Thm_LX_Core_RotationWords_recentered_lift
import Theorems.Thm_LX_Core_ZeroGap_exchange_lift
import Theorems.Thm_LX_Core_ZeroGap_exchange_short
import Theorems.Thm_LX_Core_ZeroGap_head_travel
import Theorems.Thm_LX_Core_ZeroGap_negative_endpoint_length
import Theorems.Thm_LX_Core_ZeroGap_positive_endpoint_length

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
/-! Rotations indexed by a finite cursor and their algebraic identities.
Addition and subtraction of cursors agree with permutation multiplication. -/
namespace LX.Core.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem rotation_add (a b : Fin n) : rotation (a+b)=rotation a*rotation b := by
  apply Equiv.ext
  intro i
  simp only [rotation, AffineLift.rotation_power_apply, Fin.cast_val_eq_self, Equiv.Perm.mul_apply]
  abel

theorem rotation_sub (a b : Fin n) : rotation (b-a)=(rotation a)⁻¹*rotation b := by
  have h : rotation a*rotation (b-a)=rotation b := by
    rw [← rotation_add]
    congr 1
    abel
  calc
    rotation (b-a)=(rotation a)⁻¹*(rotation a*rotation (b-a)) := by group
    _ = _ := by rw [h]


end LX.Core.RotationWords

end

section
/-! Recenter a phase lift at an arbitrary port. The local target is chosen so
that paid entry and exit rotations recover the original visible permutation. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem local_target_inverse (p : State n) (c r i : Fin n) :
    (localTarget p c r).symm i=p.symm (i+r)+(c-r) := by
  change (localTarget p c r)⁻¹ i= _
  simp only [localTarget, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply,
    AffineLift.rotation_power_apply, Fin.cast_val_eq_self]
  rfl








end LX.Core.RotationWords

end

section
/-! At phase zero, the local target is conjugation by the cursor rotation.
This identity connects recentered lifts to literal permutation products. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem local_target_zero (p : State n) (r : Fin n) :
    localTarget p 0 r=(rotation r)⁻¹*p*rotation r := by
  change (rotation r)⁻¹*p*(rotation (0-r))⁻¹= _
  rw [rotation_sub]
  simp [rotation]

end LX.Core.RotationWords

end

section
/-! Directed open arcs and the geometric condition satisfied by the ordered
list of zero-gap exchanges. Later endpoints avoid each earlier open arc. -/
namespace LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]











theorem distance_translate (u a b : Fin n) : distance (a+u) (b+u)=distance a b := by
  unfold distance
  congr 1
  ring


theorem later_outside_translate (u : Fin n) {e f : Event n} (h : LaterOutside e f) :
    LaterOutside (rotateEvent u e) (rotateEvent u f) := by
  simpa only [LaterOutside,rotateEvent,Inside,distance_translate] using h

theorem event_swap_translate (u : Fin n) (e : Event n) :
    eventSwap (rotateEvent u e)=MulAut.conj (RotationWords.rotation u) (eventSwap e) := by
  have h := Equiv.swap_apply_apply (RotationWords.rotation u) e.1 e.2
  simpa only [eventSwap,rotateEvent,RotationWords.rotation,AffineLift.rotation_power_apply,
    Fin.cast_val_eq_self,MulAut.conj_apply] using h

theorem exchange_active_subset (d : Fin n → ℤ) (v i : Fin n)
    (hpos : 0 < d 0) (hneg : d v < 0) (hi : exchange d v i ≠ 0) : d i ≠ 0 := by
  by_cases hi0 : i=0
  · subst i
    omega
  · by_cases hiv : i=v
    · subst i
      omega
    · simpa only [exchange,ite_eq_right hi0,ite_eq_right hiv] using hi

theorem zero_gap_excludes_active_event (d : Fin n → ℤ) (v : Fin n)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → d i=0)
    (e : Event n) (he : d e.1 ≠ 0 ∧ d e.2 ≠ 0) : LaterOutside (0,v) e := by
  have hdist (i : Fin n) : distance 0 i=i.val := by simp [distance]
  constructor
  · intro h
    obtain ⟨hlo,hhi⟩ := h
    simp only [hdist] at hlo hhi
    exact he.1 (hgap e.1 hlo hhi)
  · intro h
    obtain ⟨hlo,hhi⟩ := h
    simp only [hdist] at hlo hhi
    exact he.2 (hgap e.2 hlo hhi)



end LX.Core.ZeroGap

end

section
/-! Weighted paths retain the signed integer motion of tokens through the
endpoint events; their weights do not identify coordinates modulo n. -/
namespace LX.Core.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem Travel.trans {events : List (Event n)} {i j k : Fin n} {a b : ℤ}
    (h : Travel events i j a) (h' : Travel events j k b) : Travel events i k (a+b) := by
  induction h with
  | refl => simpa using h'
  | head he hp ih => simpa only [add_assoc] using Travel.head he (ih h')

theorem Travel.mono {events more : List (Event n)} (hsub : ∀ e ∈ events, e ∈ more)
    {i j : Fin n} {z : ℤ} (h : Travel events i j z) : Travel more i j z := by
  induction h with
  | refl => exact Travel.refl _
  | head he hp ih =>
    obtain ⟨e,he,hmove⟩ := he
    exact Travel.head ⟨e,hsub e he,hmove⟩ ih

theorem event_move_rotate (u : Fin n) {events : List (Event n)} {i j : Fin n} {z : ℤ}
    (h : EventMove events i j z) : EventMove (events.map (rotateEvent u)) (i+u) (j+u) z := by
  obtain ⟨e,he,h⟩ := h
  refine ⟨rotateEvent u e,List.mem_map.mpr ⟨e,he,rfl⟩,?_⟩
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl,by simp [rotateEvent,distance_translate]⟩
  · exact Or.inr ⟨rfl,rfl,by simp [rotateEvent,distance_translate]⟩

theorem Travel.rotate (u : Fin n) {events : List (Event n)} {i j : Fin n} {z : ℤ}
    (h : Travel events i j z) : Travel (events.map (rotateEvent u)) (i+u) (j+u) z := by
  induction h with
  | refl => exact Travel.refl _
  | head he hp ih => exact Travel.head (event_move_rotate u he) ih





theorem exchange_motion (d : Fin n → ℤ) (v i : Fin n) (hv : v ≠ 0) :
    headShift v i+exchange d v (Equiv.swap 0 v i)=d i := by
  by_cases hi : i=0
  · subst i
    simp [headShift,exchange,hv]
  · by_cases hiv : i=v
    · subst i
      simp [headShift,exchange,hv]
    · simp [headShift,exchange,hi,hiv,Equiv.swap_apply_of_ne_of_ne hi hiv]



end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution {p : State n} {d : Fin n → ℤ} {M : ℕ}
    (ht : SortingTrace p d M) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧ events.length=M ∧
      (∀ e ∈ events, e.1 ≠ e.2) ∧ (∀ e ∈ events, d e.1 ≠ 0 ∧ d e.2 ≠ 0) ∧
      events.Pairwise LaterOutside ∧ (∀ e ∈ events, 2*distance e.1 e.2 < n) ∧
      (∀ i, Travel events i (p.symm i) (d i)) := by
  induction ht with
  | @done p d hz =>
    have hp : p=1 := by
      apply Equiv.ext
      intro i
      have h := AffineLift.lift_residue hd (p i)
      simpa only [hz,Int.cast_zero,add_zero,p.symm_apply_apply,Equiv.Perm.one_apply] using h
    exact ⟨[],by simp [hp],rfl,by simp,by simp,List.Pairwise.nil,by simp,by intro i; simpa [hp,hz,← Equiv.Perm.inv_def] using (Travel.refl (events := []) i)⟩
  | @step p d u v hv hpos hneg hgap M ht ih =>
    have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
    have hlocal := RotationWords.recentered_lift (0 : Fin n) u (by simpa using hd)
    have hs : ∀ i, 2*|RotationWords.localDisplacement d u i| < (n : ℤ) := fun i => hshort ((L n^u.val) i)
    have hA := positive_endpoint_length hlocal v hpos hgap
    have hB := negative_endpoint_length hlocal v hneg hgap
    have hvshort : 2*v.val < n := by
      have h := hs 0
      rw [abs_of_pos hpos] at h
      omega
    obtain ⟨events,hprod,hlen,hneq,hactive,hsep,hshortEvents,htravel⟩ := ih (exchange_lift hlocal v hv0)
      (exchange_short _ v hv0 hA hB hs)
    let base := (0,v)::events
    let result := base.map (rotateEvent u)
    have hbase_active : ∀ e ∈ base,
        RotationWords.localDisplacement d u e.1 ≠ 0 ∧ RotationWords.localDisplacement d u e.2 ≠ 0 := by
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact ⟨ne_of_gt hpos,ne_of_lt hneg⟩
      · have he' := hactive e he
        exact ⟨exchange_active_subset _ v e.1 hpos hneg he'.1,
          exchange_active_subset _ v e.2 hpos hneg he'.2⟩
    have hbase_neq : ∀ e ∈ base, e.1 ≠ e.2 := by
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact Ne.symm hv0
      · exact hneq e he
    have hbase_sep : base.Pairwise LaterOutside := List.Pairwise.cons
      (fun e he => zero_gap_excludes_active_event _ v hgap e (hbase_active e (List.mem_cons_of_mem _ he))) hsep
    have hbase_prod : (base.map eventSwap).prod=RotationWords.localTarget p 0 u := by
      simp only [base,List.map_cons,List.prod_cons,eventSwap,hprod,← mul_assoc,Equiv.swap_mul_self,one_mul]
    have hbase_travel : ∀ i, Travel base i ((RotationWords.localTarget p 0 u).symm i)
        (RotationWords.localDisplacement d u i) := by
      intro i
      have ht := (htravel (Equiv.swap 0 v i)).mono
        (fun e he => List.mem_cons_of_mem (0,v) he)
      have hj : (Equiv.swap 0 v * RotationWords.localTarget p 0 u).symm
          (Equiv.swap 0 v i) = (RotationWords.localTarget p 0 u).symm i := by
        change (Equiv.swap 0 v * RotationWords.localTarget p 0 u)⁻¹
          (Equiv.swap 0 v i) = (RotationWords.localTarget p 0 u)⁻¹ i
        simp [Equiv.Perm.mul_apply]
      rw [hj] at ht
      have hpath := (head_travel v i events).trans ht
      rw [exchange_motion _ v i hv0] at hpath
      exact hpath
    refine ⟨result,?_,?_,?_,?_,?_,?_,?_⟩
    · calc
        (result.map eventSwap).prod = ((base.map eventSwap).map (MulAut.conj (RotationWords.rotation u))).prod := by
          simp only [result,List.map_map,Function.comp_def,event_swap_translate]
        _ = MulAut.conj (RotationWords.rotation u) ((base.map eventSwap).prod) := (map_list_prod _ _).symm
        _ = p := by
          rw [hbase_prod,RotationWords.local_target_zero,MulAut.conj_apply]
          group
    · simp only [result,List.length_map,base,List.length_cons,hlen]
    · intro e he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      exact fun h => hbase_neq f hf (add_right_cancel h)
    · intro e he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      have h := hbase_active f hf
      simpa only [rotateEvent,RotationWords.localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self] using h
    · apply List.pairwise_map.mpr
      exact hbase_sep.imp (fun h => later_outside_translate u h)
    · intro e he
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
      simp only [rotateEvent,distance_translate]
      rcases List.mem_cons.mp hf with hf | hf
      · subst f
        simpa [distance] using hvshort
      · exact hshortEvents f hf

    · intro j
      have hpath := (hbase_travel (j-u)).rotate u
      have hi : j-u+u=j := sub_add_cancel j u
      have hj : (RotationWords.localTarget p 0 u).symm (j-u)+u=p.symm j := by
        rw [RotationWords.local_target_inverse]
        simp
      have hdj : RotationWords.localDisplacement d u (j-u)=d j := by
        simp [RotationWords.localDisplacement,AffineLift.rotation_power_apply]
      rw [hi,hj,hdj] at hpath
      exact hpath
