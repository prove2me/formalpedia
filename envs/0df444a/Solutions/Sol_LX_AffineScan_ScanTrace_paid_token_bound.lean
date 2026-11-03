-- Prove2me | solution 1 for LX.AffineScan.ScanTrace.paid_token_bound
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:40:01.738969+00:00
-- url     : https://prove2.me/submissions/629ff93b-fc66-48de-a424-8d90e18f512d

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
import Definitions.Def_LX_DirectedTokenLower
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_Core_LiftedModel_step_aligned
import Theorems.Thm_LX_LiftedScan_exact_positions_of_zero

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Antipode
end LX.Antipode
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
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
namespace LX.Core.WordReflection
end LX.Core.WordReflection
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
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


































theorem run_append (u v : List Letter) (d : Fin n → ℤ) :
    run (u ++ v) d = run v (run u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons a u ih => exact ih (step a d)











theorem run_left_apply (k : ℕ) (d : Fin n → ℤ) (i : Fin n) :
    run (List.replicate k .l) d i = d (((LX.Core.L n)^k) i) := by
  induction k generalizing d with
  | zero => simp [run]
  | succ k ih =>
    simp only [List.replicate_succ, run, step]
    rw [ih]
    simp only [rotate, LX.Core.L, pow_succ', Equiv.Perm.mul_apply]







end LX.AffineScan

end

section
namespace LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.LiftedModel
variable {n : ℕ} [NeZero n]



theorem token_budget_step (hn : 2 ≤ n) (a : Letter) (s : Configuration n)
    (hs : Aligned s) (hb : TokenBudget s) : TokenBudget (step a.toCore s) := by
  intro i
  have hi := hb i
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  cases a with
  | l =>
    simp only [Letter.toCore,step,increment]
    linarith
  | x =>
    by_cases hleft : i=s.physical.tokens s.physical.cursor
    · have hright : i ≠ s.physical.tokens (s.physical.cursor+1) := by
        intro he
        exact neighboring_positions_distinct hn s.physical.cursor
          (s.physical.tokens.injective (hleft.symm.trans he))
      simp only [Letter.toCore,step,increment,ite_eq_left hleft,ite_eq_right hright,sub_zero,add_zero]
      nlinarith only [hi,hn']
    · by_cases hright : i=s.physical.tokens (s.physical.cursor+1)
      · have hz : (s.position i : Fin n)=(s.cursor : Fin n)+1 := by
          rw [hs.2 i,hright,Equiv.symm_apply_apply,hs.1]
        have hmod : ((s.cursor+((n : ℤ)-1)*s.position i+1 : ℤ) : Fin n)=0 := by
          simp only [Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast,
            Fin.natCast_self,Int.cast_one,hz]
          ring
        have hdiv : (n : ℤ) ∣ s.cursor+((n : ℤ)-1)*s.position i+1 :=
          Int.modEq_zero_iff_dvd.mp ((cast_eq_iff_modEq _ 0).mp (by simpa using hmod))
        obtain ⟨k,hk⟩ := hdiv
        have hklo : ((i.val-1 : ℕ) : ℤ)+1 ≤ k := by
          by_contra hnot
          have hle : k ≤ ((i.val-1 : ℕ) : ℤ) := by omega
          have hmul := mul_le_mul_of_nonneg_left hle (show (0 : ℤ) ≤ n by omega)
          nlinarith only [hi,hk,hmul]
        have hmul := mul_le_mul_of_nonneg_left hklo (show (0 : ℤ) ≤ n by omega)
        simp only [Letter.toCore,step,increment,ite_eq_right hleft,ite_eq_left hright,add_zero]
        nlinarith only [hk,hmul]
      · simpa only [Letter.toCore,step,increment,ite_eq_right hleft,ite_eq_right hright,add_zero,sub_zero] using hi

theorem token_budget_initial : TokenBudget (initial (n := n)) := by
  intro i
  have hi : (i : ℤ) < n := by exact_mod_cast i.isLt
  simp only [initial,zero_add]
  by_cases hz : i.val=0
  · simp [hz]
  · rw [Nat.cast_sub (by omega : 1 ≤ i.val)]
    push_cast
    nlinarith only [hi]

theorem token_budget_run (hn : 2 ≤ n) (w : List Letter) (s : Configuration n)
    (hs : Aligned s) (hb : TokenBudget s) : TokenBudget (run (w.map Letter.toCore) s) := by
  induction w generalizing s with
  | nil => exact hb
  | cons a w ih =>
    exact ih (step a.toCore s) (step_aligned hn a.toCore hs) (token_budget_step hn a s hs hb)

/-- An unconditional rotation lower bound for every token of every
literal LX word, expressed in its exact integer endpoint. -/
theorem word_cursor_lower (hn : 2 ≤ n) (w : List Letter) (i : Fin n) :
    (n : ℤ)*(i.val-1 : ℕ)-((n : ℤ)-1)*(run (w.map Letter.toCore) (initial (n := n))).position i ≤
      (run (w.map Letter.toCore) (initial (n := n))).cursor := by
  have hb := token_budget_run hn w initial initial_aligned token_budget_initial i
  omega

theorem cursor_eq_left_count (w : List Letter) :
    (run (w.map Letter.toCore) (initial (n := n))).cursor=(w.count .l : ℤ) := by
  rw [cursor_run]
  simp only [initial,zero_add,List.map_map]
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [Letter.toCore,increment,ih,add_comm]









end LX.DirectedTokenLower

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

theorem paid_rotations_phase (c : Fin n) (g : List Letter) :
    (paidRotations c g : Fin n)=c := by
  simp only [paidRotations,Nat.cast_add,Fin.cast_val_eq_self]
  ring



end LX.AffineScan

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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The endpoint residue pays the exact extra rotation missing from the
plain token budget. All quantities come from the same literal word. -/
theorem solution (hn : 2 ≤ n) {p : State n} {c : Fin n}
    {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift p (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) (i : Fin n) :
    (n : ℤ)*(i.val-1 : ℕ)-((n : ℤ)-1)*targets d i+((-p.symm i : Fin n) : ℤ) ≤
      (paidRotations c g : ℤ) := by
  have hz (j : Fin n) : run (paidWord c g) d j=0 := by
    simp only [paidWord,run_append,run_left_apply]
    exact hg.run_zero _
  have hcount : (paidWord c g).count .l=paidRotations c g := by simp [paidWord,paidRotations]
  have ht := DirectedTokenLower.word_cursor_lower hn (paidWord c g) i
  rw [LiftedScan.exact_positions_of_zero hn d (paidWord c g) hz i,
    DirectedTokenLower.cursor_eq_left_count,hcount] at ht
  let T : ℤ := (n : ℤ)*(i.val-1 : ℕ)-((n : ℤ)-1)*targets d i
  let R : ℤ := (paidRotations c g : ℤ)
  have hnonneg : 0 ≤ R-T := by change T ≤ R at ht; omega
  have hF : (targets d i : Fin n)=p.symm i+c := by
    simpa only [targets,Int.cast_add,Int.cast_natCast,Fin.cast_val_eq_self] using
      LX.Core.AffineLift.lift_residue hd i
  have hphase := paid_rotations_phase c g
  have hcast : ((R-T : ℤ) : Fin n)= -p.symm i := by
    simp only [R,T,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Fin.natCast_self,
      Int.cast_one,hF,hphase]
    ring
  have hr := Int.emod_nonneg (R-T) (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)
  have hq := Int.ediv_nonneg hnonneg (show (0 : ℤ) ≤ n by positivity)
  have he := Int.ediv_mul_add_emod (R-T) (n : ℤ)
  have hval : (((R-T : ℤ) : Fin n) : ℤ) ≤ R-T := by
    simp only [Fin.val_intCast,Int.toNat_of_nonneg hr]
    have hm := mul_nonneg hq (show (0 : ℤ) ≤ n by positivity)
    omega
  rw [hcast] at hval
  change T+((-p.symm i : Fin n) : ℤ) ≤ R
  omega
