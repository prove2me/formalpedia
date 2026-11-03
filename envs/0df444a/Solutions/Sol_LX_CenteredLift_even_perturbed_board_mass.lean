-- Prove2me | solution 1 for LX.CenteredLift.even_perturbed_board_mass
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:07:03.571819+00:00
-- url     : https://prove2.me/submissions/46b5a651-9632-470e-a128-71533b70ced2

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
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_CenteredLift_even_reflection_board_formula
import Theorems.Thm_LX_CenteredLift_even_reflection_board_sum

namespace Int
end Int
namespace LX
end LX
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
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
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem center_bounds (m : ℕ) (z : ℤ) :
    -(m : ℤ) ≤ center (n := n) m z ∧ center (n := n) m z < (n : ℤ)-m := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hlo := Int.emod_nonneg (z+m) (ne_of_gt hn)
  have hhi := Int.emod_lt_of_pos (z+m) hn
  unfold center
  omega



theorem center_add (m : ℕ) (z t : ℤ) :
    center (n := n) m (z+t)=center (n := n) m (center (n := n) m z+t) := by
  unfold center
  have h1 : z+t+m=(z+m)+t := by ring
  have h2 : (z+m)%(n : ℤ)-m+t+m=(z+m)%(n : ℤ)+t := by ring
  rw [h1,h2]
  simp only [Int.add_emod,Int.emod_emod]

theorem le_center_of_below_top (m : ℕ) (z : ℤ) (hz : z < (n : ℤ)-m) :
    z ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (1 : ℤ)*n by omega)
  have hm := mul_nonpos_of_nonpos_of_nonneg (show (z+m)/(n : ℤ) ≤ 0 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  omega

theorem sub_period_le_center_of_at_top (m : ℕ) (z : ℤ) (hz : z ≤ (n : ℤ)-m) :
    z-n ≤ center (n := n) m z := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hq := (Int.ediv_lt_iff_lt_mul hn).mpr (show z+m < (2 : ℤ)*n by omega)
  have hm := mul_le_mul_of_nonneg_right (show (z+m)/(n : ℤ) ≤ 1 by omega) (le_of_lt hn)
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  nlinarith

/-- Increasing an input by at most one can wrap down only at the top
representative. Larger downward changes can only increase the remainder. -/
theorem center_perturb_lower (m : ℕ) (z t : ℤ) (ht : t ≤ 1) :
    center (n := n) m z+t-(if center (n := n) m z=(n : ℤ)-m-1 then n else 0) ≤
      center (n := n) m (z+t) := by
  rw [center_add]
  have hb := center_bounds (n := n) m z
  by_cases he : center (n := n) m z=(n : ℤ)-m-1
  · rw [ite_eq_left he]
    exact sub_period_le_center_of_at_top m _ (by omega)
  · rw [ite_eq_right he,Nat.cast_zero,sub_zero]
    exact le_center_of_below_top m _ (by omega)






end LX.CenteredLift

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

namespace LX.CenteredLift
end LX.CenteredLift
open LX
open LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The transposition of ranks 1 and 2 still leaves centered mass at
least -n. Its only possible downward wrap occurs when the base mass is zero. -/
theorem solution (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (C : ℤ) :
    -(n : ℤ) ≤ ∑ i : Fin n,perturbedBoard m C (Equiv.swap 1 2) i := by
  let ρ : State n := Equiv.swap 1 2
  let e : Fin n → ℤ := reflectionBoard m C
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have h12 : (1 : Fin n) ≠ 2 := by intro hh; have := congrArg Fin.val hh; omega
  have hp (i : Fin n) : e i+((i : ℤ)-(ρ i : ℤ))-
      (if i=2 ∧ e 2=(n : ℤ)-m-1 then (n : ℤ) else 0) ≤ perturbedBoard m C ρ i := by
    have hex : C-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=C-(ρ i : ℤ)-(i : ℤ) := by ring
    by_cases hi2 : i=2
    · subst i
      have hh := center_perturb_lower (n := n) m (C-2*(2 : Fin n).val)
        ((2 : Fin n).val-(ρ 2 : ℤ)) (by simp only [ρ,Equiv.swap_apply_right,hv1,hv2]; omega)
      rw [hex] at hh
      convert hh using 1 <;>
        simp only [true_and,Nat.cast_ite,Nat.cast_zero,e,reflectionBoard,perturbedBoard] <;> rfl
    · have hδ : (i : ℤ)-(ρ i : ℤ) ≤ 0 := by
        by_cases hi1 : i=1
        · subst i; simp only [ρ,Equiv.swap_apply_left,hv1,hv2]; omega
        · simp only [ρ,Equiv.swap_apply_of_ne_of_ne hi1 hi2,sub_self,le_refl]
      have hb := center_bounds (n := n) m (C-2*(i : ℤ))
      have hh := le_center_of_below_top (n := n) m (e i+((i : ℤ)-(ρ i : ℤ))) (by
        have hbe : e i < (n : ℤ)-m := hb.2
        linarith)
      dsimp only [e,reflectionBoard] at hh
      rw [← center_add] at hh
      rw [hex] at hh
      simpa only [hi2,false_and,ite_false,sub_zero,e,reflectionBoard,perturbedBoard] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have hsum : (∑ i : Fin n,e i)=(n : ℤ)*((C+m)%2-1) := even_reflection_board_sum m (by omega) hn C
  have hloss : (∑ i : Fin n,if i=2 ∧ e 2=(n : ℤ)-m-1 then (n : ℤ) else 0)=
      if e 2=(n : ℤ)-m-1 then n else 0 := by simp [ite_and]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,hδ,hsum,hloss,add_zero] at hs
  change -(n : ℤ) ≤ ∑ i : Fin n,perturbedBoard m C ρ i
  by_cases htop : e 2=(n : ℤ)-m-1
  · have hformula := even_reflection_board_formula m (by omega) hn C (2 : Fin n)
    change e 2=_ at hformula
    rw [htop] at hformula
    have hpar : (C+m)%2=1 := by omega
    rw [hpar,ite_eq_left htop] at hs
    norm_num at hs
    exact hs
  · rw [ite_eq_right htop,Nat.cast_zero,sub_zero] at hs
    have hr : 0 ≤ (C+m)%2 := Int.emod_nonneg _ (by decide)
    have hp := mul_nonneg (show (0 : ℤ) ≤ n by positivity) hr
    nlinarith
