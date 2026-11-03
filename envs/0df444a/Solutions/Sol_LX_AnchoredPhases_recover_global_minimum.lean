-- Prove2me | solution 1 for LX.AnchoredPhases.recover_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:13:10.272292+00:00
-- url     : https://prove2.me/submissions/1fd45f38-75f6-4c07-98d7-9630da0f8f44

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
import Definitions.Def_LX_AnchoredPhases
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_MinimumEnergyPhases
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_AnchoredPhases_recovers_strict_strip
import Theorems.Thm_LX_Core_AffineLift_short_coordinates

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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators





theorem energy_cast {n : ℕ} (d : Fin n → ℤ) :
    (energy d : ℤ) = ∑ i, d i ^ 2 := by
  simp [energy, sq_abs]







theorem shift_balanced {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n))
    (hd : ∑ i, d i = 0) : ∑ i, phaseShift d s i = 0 := by
  simp [phaseShift, Finset.sum_sub_distrib, Finset.sum_add_distrib, hd,
    Finset.sum_ite_mem, mul_comm]

theorem shift_lift {n : ℕ} {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (s : Finset (Fin n)) :
    IsLift p (c + s.card) (phaseShift d s) := by
  refine ⟨shift_balanced d s hd.1, ?_⟩
  intro i
  have h := (hd.2 i).add_right (s.card : ℤ)
  simp only [phaseShift]
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    rw [← add_sub_assoc, Int.sub_modulus_modEq_iff]
    simpa only [add_assoc] using h
  · simp only [ite_eq_right hi, sub_zero]
    simpa only [add_assoc] using h

/-- The exact change in quadratic energy for every subset, not just sorted prefixes. -/
theorem shift_energy {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n))
    (hd : ∑ i, d i = 0) :
    (energy (phaseShift d s) : ℤ) - energy d =
      (n : ℤ) * ((s.card : ℤ) * (n - s.card) - 2 * ∑ i ∈ s, d i) := by
  rw [energy_cast, energy_cast]
  have point (i : Fin n) : phaseShift d s i ^ 2 =
      d i ^ 2 + 2 * (s.card : ℤ) * d i + (s.card : ℤ) ^ 2 +
      if i ∈ s then (n : ℤ)^2 - 2*n*s.card - 2*n*d i else 0 := by
    unfold phaseShift
    split_ifs <;> ring
  simp_rw [point]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_mem, hd]
  ring



theorem minimal_majorized {n : ℕ} (hn : 0 < n) {p : State n} {c : ℤ}
    {d : Fin n → ℤ} (hd : IsLift p c d)
    (hmin : ∀ c' d', IsLift p c' d' → energy d ≤ energy d') : Majorized d := by
  intro s
  have h := hmin _ _ (shift_lift hd s)
  have he : (energy d : ℤ) ≤ energy (phaseShift d s) := by exact_mod_cast h
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hprod : 0 ≤ (n : ℤ) *
      ((s.card : ℤ) * (n - s.card) - 2 * ∑ i ∈ s, d i) := by
    rw [← shift_energy d s hd.1]
    omega
  have hnonneg := nonneg_of_mul_nonneg_right hprod hn'
  omega




theorem range_bound {n : ℕ} {d : Fin n → ℤ}
    (hd : ∑ i, d i = 0) (hm : Majorized d) (i j : Fin n) :
    d i - d j ≤ (n : ℤ) - 1 := by
  obtain ⟨hi, _⟩ := short_coordinates hd hm i
  obtain ⟨_, hj⟩ := short_coordinates hd hm j
  omega

end LX.Core.AffineLift

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

namespace LX.AnchoredPhases
end LX.AnchoredPhases
open LX
open LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem solution {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p.symm c d) (hm : ∀ c' d', IsLift p.symm c' d' → energy d ≤ energy d') :
    ∃ a : Fin n, _root_.LX.AnchoredPhases.displacement p a=d ∧ (phase p a : Fin n)=(c : Fin n) ∧ GlobalMinimum p a := by
  have hmajor := minimal_majorized (NeZero.pos n) hd hm
  obtain ⟨a,_,ha⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) d
    ⟨0,Finset.mem_univ _⟩
  have hh := recovers_strict_strip hd a (fun i => ha i (Finset.mem_univ _)) (by
    intro i
    have hw := range_bound hd.1 hmajor i a
    omega)
  refine ⟨a,hh.1,hh.2,?_⟩
  intro c' d' hd'
  rw [hh.1]
  exact hm c' d' hd'
