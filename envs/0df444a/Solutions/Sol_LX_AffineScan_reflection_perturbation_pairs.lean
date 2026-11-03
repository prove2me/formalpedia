-- Prove2me | solution 1 for LX.AffineScan.reflection_perturbation_pairs
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:40:02.405486+00:00
-- url     : https://prove2.me/submissions/dbbb46f9-06d6-4f33-b2de-aabc52327ec6

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
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoColorPairs
import Definitions.Def_LX_WordMetric

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
/-! Integer division is determined by lower and upper quotient bounds.
This arithmetic identity is used in the finite-coordinate estimates. -/
namespace LX.Core.PeriodicBuffer

theorem quotient_eq_of_bounds {M x q : ℤ} (hM : 0 < M)
    (hlo : q*M ≤ x) (hhi : x < (q+1)*M) : x/M = q := by
  have ha := (Int.le_ediv_iff_mul_le hM).mpr hlo
  have hb := (Int.ediv_lt_iff_lt_mul hM).mpr hhi
  omega


end LX.Core.PeriodicBuffer

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

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Winding parity forces a crossing for every unreversed pair of equal
color. A finite perturbation of the reflection can lose only its own
finite inversion count. No minimum-energy hypothesis is used. -/
theorem solution (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    sameColorPairs (fun i => decide (k i % 2=0)) ≤
      inversions d+LX.Core.FiniteCuts.inversionNumber ρ := by
  let χ : Fin n → Bool := fun i => decide (k i % 2=0)
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hp (i j : Fin n) : (if i < j ∧ χ i=χ j then 1 else 0) ≤
      (if i < j then ((targets d j-targets d i)/(n : ℤ)).natAbs else 0)+
      (if i.val < j.val ∧ (ρ j).val < (ρ i).val then 1 else 0 : ℕ) := by
    by_cases hpair : i < j ∧ χ i=χ j
    · rw [ite_eq_left hpair,ite_eq_left hpair.1]
      by_cases hr : (ρ j).val < (ρ i).val
      · rw [ite_eq_left ⟨hpair.1,hr⟩]; omega
      · rw [ite_eq_right (by omega : ¬(i.val < j.val ∧ (ρ j).val < (ρ i).val)),add_zero]
        have hne : ρ i ≠ ρ j := fun hh => (ne_of_lt hpair.1) (ρ.injective hh)
        have hlt : (ρ i : ℤ) < ρ j := by
          have hvals : (ρ i).val ≠ (ρ j).val := fun hh => hne (Fin.ext hh)
          omega
        have hq : (targets d j-targets d i)/(n : ℤ)=k j-k i-1 := by
          rw [hF j,hF i]
          apply LX.Core.PeriodicBuffer.quotient_eq_of_bounds hn
          · have hi := (ρ i).isLt
            have hj := (ρ j).isLt
            nlinarith
          · nlinarith
        have hcolor : (k i % 2=0) ↔ (k j % 2=0) := by
          simpa only [χ,decide_eq_decide] using hpair.2
        have hmod : k i % 2=k j % 2 := by omega
        have hne0 : k j-k i-1 ≠ 0 := by omega
        rw [hq]
        exact Int.natAbs_pos.mpr hne0
    · rw [ite_eq_right hpair]; exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp i j))
  simpa only [Finset.sum_add_distrib,sameColorPairs,inversions,LX.Core.LiftedModel.inversionCount,
    LX.Core.FiniteCuts.inversionNumber,χ] using hs
