-- Prove2me | solution 1 for LX.Antipode.even_unpaid_bottom_positions
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:46:47.269533+00:00
-- url     : https://prove2.me/submissions/e1300006-c256-4ad1-95a7-574d4f8e4a99

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
import Definitions.Def_LX_AntipodeCandidates
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoColorPairs
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_AffineScan_ScanTrace_paid_token_bound
import Theorems.Thm_LX_AffineScan_exists_reflection_winding
import Theorems.Thm_LX_AffineScan_reflection_perturbation_pairs
import Theorems.Thm_LX_Antipode_even_bottom_ordinary_paid
import Theorems.Thm_LX_Core_FiniteCuts_adjacent_swap_inversion_price
import Theorems.Thm_LX_even_same_color_pairs_lower

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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem even_reflection_lift_inversions_lower (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ) (m : ℕ) (hn : n=2*m)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    m*(m-1) ≤ inversions d+LX.Core.FiniteCuts.inversionNumber ρ :=
  (even_same_color_pairs_lower _ m hn).trans (reflection_perturbation_pairs d ρ C k hF)





theorem even_reflection_lift_lower {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (ρ : State n)
    (hp : ∀ i,p.symm i=1-ρ i) (m : ℕ) (hn : n=2*m) :
    m*(m-1) ≤ inversions d+LX.Core.FiniteCuts.inversionNumber ρ := by
  obtain ⟨k,hk⟩ := exists_reflection_winding hd ρ hp
  exact even_reflection_lift_inversions_lower d ρ (c+1) k m hn hk







end LX.AffineScan

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
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]











theorem even_rank_inversions (hn : 3 ≤ n) : inversionNumber (Equiv.swap (1 : Fin n) 2)=1 := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hh := adjacent_swap_inversion_price (Equiv.swap (1 : Fin n) 2) 1 2
    (by rw [hv1,hv2]) (by simp only [Equiv.swap_apply_left,Equiv.swap_apply_right,hv1,hv2]; omega)
  have he : (Equiv.swap (1 : Fin n) 2)*Equiv.swap 1 2=1 := Equiv.swap_mul_self _ _
  rw [he] at hh
  have hz : inversionNumber (1 : State n)=0 := by
    unfold inversionNumber
    simp only [Equiv.Perm.one_apply]
    have hp (i j : Fin n) : ¬(i.val < j.val ∧ j.val < i.val) := by omega
    simp only [hp,ite_false,Finset.sum_const_zero]
  omega



/-- Uniform exchange lower bound for every lift and every phase of the
even candidate. -/
theorem even_lift_inversions_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : ℤ} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even c d) :
    m*(m-1) ≤ inversions d+1 := by
  have hp (i : Fin n) : (even : State n).symm i=1-(Equiv.swap (1 : Fin n) 2) i := rfl
  have hh := even_reflection_lift_lower hd (Equiv.swap 1 2) hp m hn
  rwa [even_rank_inversions (by omega : 3 ≤ n)] at hh





end LX.Antipode

end

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem solution (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-4*m+3)
    (i : Fin n) (hdi : d i= -(m : ℤ)) : i.val=1 ∨ i.val=2 := by
  by_cases hi0 : i.val=0
  · have ht := hg.paid_token_bound (by omega : 2 ≤ n) hd i
    have hqnonneg : (0 : ℤ) ≤ ((-(even : State n).symm i : Fin n) : ℤ) := by positivity
    simp only [targets,hdi,hi0,Nat.zero_sub,Nat.cast_zero,zero_add,mul_zero,zero_sub] at ht
    have hI := even_lift_inversions_lower m hm hn hd
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ) ≤ (inversions d : ℤ)+1 := by exact_mod_cast hI
    have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-4*m+3 : ℕ) : ℤ) := by
      exact_mod_cast hu
    have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
    rw [hm1] at hI'
    rw [Nat.cast_add,Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)] at hu'
    push_cast at hu'
    have hn' : (n : ℤ)=2*m := by omega
    have hm' : (3 : ℤ) ≤ m := by omega
    nlinarith
  · by_contra hnot
    have hh := even_bottom_ordinary_paid m hm hn hd hg i (by omega) hdi
    omega
