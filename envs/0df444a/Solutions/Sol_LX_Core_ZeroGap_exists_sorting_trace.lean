-- Prove2me | solution 1 for LX.Core.ZeroGap.exists_sorting_trace
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:45:16.642906+00:00
-- url     : https://prove2.me/submissions/5eea4880-f55c-4bde-93d3-b10b7faacbe7

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
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ZeroGapExchange
import Definitions.Def_LX_ZeroGapSorting
import Theorems.Thm_LX_Core_ZeroGap_exists_descent

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
/-! The inversion terms reversed by a zero-gap endpoint swap each drop from
one to zero. Other endpoint terms are exchanged in pairs. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem nonnegative_quotient_term {z : ℤ} (hz : 0 ≤ z) (hn : z < (n : ℤ)) : (z/(n : ℤ)).natAbs=0 := by
  rw [Int.ediv_eq_zero_of_lt hz hn]
  decide







end LX.Core.ZeroGap

end

section
/-! Termination of the zero-gap sorting process and its exact number of
endpoint transpositions. Recentring is part of the mathematical trace. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem mass_cast (d : Fin n → ℤ) : (mass d : ℤ)=∑ i : Fin n, |d i| := by
  simp only [mass,Nat.cast_sum,Int.natCast_natAbs]



theorem identity_inversions : LiftedModel.inversionCount (fun i : Fin n => (i : ℤ))=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  change (if i < j then (((j : ℤ)-(i : ℤ))/(n : ℤ)).natAbs else 0)=0
  by_cases hij : i < j
  · rw [ite_eq_left hij]
    apply nonnegative_quotient_term
    · have h : (i : ℤ) < j := by exact_mod_cast hij
      omega
    · have hi : (0 : ℤ) ≤ i := by positivity
      have hj : (j : ℤ) < n := by exact_mod_cast j.isLt
      omega
  · rw [ite_eq_right hij]





end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) :
    ∃ M : ℕ, SortingTrace p d M ∧
      (∑ i : Fin n, |d i|)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+M := by
  have main : ∀ m : ℕ, ∀ p : State n, ∀ d : Fin n → ℤ, mass d=m →
      AffineLift.IsLift p 0 d → (∀ i, 2*|d i| < (n : ℤ)) →
      ∃ M : ℕ, SortingTrace p d M ∧
        (∑ i : Fin n, |d i|)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+M := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p d hmass hd hs
      by_cases hne : ∃ i, d i ≠ 0
      · obtain ⟨u,v,hv,hpos,hneg,hgap,hd',hs',hm,hC⟩ := exists_descent hd hs hne
        have hsmaller : mass (exchange (RotationWords.localDisplacement d u) v) < m := by
          have h0 := mass_cast d
          have h1 := mass_cast (exchange (RotationWords.localDisplacement d u) v)
          rw [hmass] at h0
          omega
        obtain ⟨M,htrace,hcount⟩ := ih _ hsmaller _ _ rfl hd' hs'
        refine ⟨M+1,SortingTrace.step u v hv hpos hneg hgap htrace,?_⟩
        have hC' := congrArg (fun k : ℕ => (k : ℤ)) hC
        push_cast at hC'
        omega
      · have hz : ∀ i, d i=0 := by intro i; by_contra h; exact hne ⟨i,h⟩
        refine ⟨0,SortingTrace.done hz,?_⟩
        simp only [hz,abs_zero,Finset.sum_const_zero,add_zero,identity_inversions,Nat.cast_zero]
  exact main (mass d) p d rfl hd hshort
