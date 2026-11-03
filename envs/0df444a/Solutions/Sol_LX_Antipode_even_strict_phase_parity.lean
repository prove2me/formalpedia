-- Prove2me | solution 1 for LX.Antipode.even_strict_phase_parity
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:15:44.098356+00:00
-- url     : https://prove2.me/submissions/48e828a3-551d-441a-939b-de26ab8ef40f

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
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_EvenStrictBase
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_Antipode_even_strict_lift_unique
import Theorems.Thm_LX_CenteredLift_even_reflection_board_sum

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
namespace LX.ForwardCarrier
end LX.ForwardCarrier
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

theorem center_cast (m : ℕ) (z : ℤ) : ((center (n := n) m z : ℤ) : Fin n)=(z : Fin n) := by
  apply (LX.Core.LiftedModel.cast_eq_iff_modEq _ _).mpr
  apply Int.modEq_iff_dvd.mpr
  refine ⟨(z+m)/(n : ℤ),?_⟩
  have he := Int.ediv_mul_add_emod (z+m) (n : ℤ)
  unfold center
  nlinarith

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
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem center_predecessor (m : ℕ) (hm : 1 ≤ m) (z : ℤ) :
    center (n := n) (m-1) z=center (n := n) m (z-1)+1 := by
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have he : z+((m-1 : ℕ) : ℤ)=(z-1)+m := by omega
  unfold center
  rw [he]
  omega

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]













end LX.Antipode

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
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem swap_perturbed_mass_drop (h : ℕ) (hn : 3 ≤ n) (C : ℤ) :
    (∑ i : Fin n,reflectionBoard h C i)-
      (if reflectionBoard h C (2 : Fin n)=(n : ℤ)-h-1 then (n : ℤ) else 0) ≤
        ∑ i : Fin n,perturbedBoard h C (Equiv.swap 1 2) i := by
  let ρ : State n := Equiv.swap 1 2
  let e : Fin n → ℤ := reflectionBoard h C
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hp (i : Fin n) : e i+((i : ℤ)-(ρ i : ℤ))-
      (if i=2 ∧ e 2=(n : ℤ)-h-1 then (n : ℤ) else 0) ≤ perturbedBoard h C ρ i := by
    have hex : C-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=C-(ρ i : ℤ)-(i : ℤ) := by ring
    by_cases hi2 : i=2
    · subst i
      have hh := center_perturb_lower (n := n) h (C-2*(2 : Fin n).val)
        ((2 : Fin n).val-(ρ 2 : ℤ)) (by simp only [ρ,Equiv.swap_apply_right,hv1,hv2]; omega)
      rw [hex] at hh
      convert hh using 1 <;>
        simp only [true_and,Nat.cast_ite,Nat.cast_zero,e,reflectionBoard,perturbedBoard]
    · have hδ : (i : ℤ)-(ρ i : ℤ) ≤ 0 := by
        by_cases hi1 : i=1
        · subst i; simp only [ρ,Equiv.swap_apply_left,hv1,hv2]; omega
        · simp only [ρ,Equiv.swap_apply_of_ne_of_ne hi1 hi2,sub_self,le_refl]
      have hb : e i < (n : ℤ)-h := (center_bounds (n := n) h (C-2*(i : ℤ))).2
      have hh := le_center_of_below_top (n := n) h (e i+((i : ℤ)-(ρ i : ℤ))) (by omega)
      dsimp only [e,reflectionBoard] at hh
      rw [← center_add,hex] at hh
      simpa only [hi2,false_and,ite_false,sub_zero,e,reflectionBoard,perturbedBoard] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have hloss : (∑ i : Fin n,if i=2 ∧ e 2=(n : ℤ)-h-1 then (n : ℤ) else 0)=
      if e 2=(n : ℤ)-h-1 then (n : ℤ) else 0 := by simp [ite_and]
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,hδ,hloss,add_zero] using hs

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem even_strict_reflection_mass (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) (c : Fin n) :
    (∑ i : Fin n,reflectionBoard (m-1) ((c : ℤ)+1) i)=(n : ℤ)*(((c : ℤ)+m)%2) := by
  have hp (i : Fin n) : reflectionBoard (m-1) ((c : ℤ)+1) i=reflectionBoard m (c : ℤ) i+1 := by
    unfold reflectionBoard
    rw [center_predecessor m (by omega)]
    congr 2
    ring
  simp only [hp,Finset.sum_add_distrib,even_reflection_board_sum m (by omega) hn,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

theorem even_strict_top_phase (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) (c : Fin n)
    (ht : reflectionBoard (m-1) ((c : ℤ)+1) (2 : Fin n)=(n : ℤ)-(m-1 : ℕ)-1) :
    c=((m+3 : ℕ) : Fin n) := by
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have he := center_cast (n := n) (m-1) ((c : ℤ)+1-2*((2 : Fin n) : ℤ))
  change (reflectionBoard (m-1) ((c : ℤ)+1) (2 : Fin n) : Fin n)=_ at he
  rw [ht] at he
  have htop : (n : ℤ)-(m-1 : ℕ)-1=(m : ℤ) := by omega
  rw [htop] at he
  simp only [hv2,Nat.cast_ofNat,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_one,
    Int.cast_ofNat,Int.cast_natCast,Fin.cast_val_eq_self,Nat.cast_add] at he ⊢
  linear_combination -he







end LX.Antipode

end

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem solution (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hlo : ∀ i,1-(m : ℤ) ≤ d i) :
    c=((m+3 : ℕ) : Fin n) ∨ (c.val+m)%2=0 := by
  by_cases hc : c=((m+3 : ℕ) : Fin n)
  · exact Or.inl hc
  · right
    have he := even_strict_lift_unique m (by omega) hn c hd hlo
    have hz := hd.1
    rw [he] at hz
    have hs := swap_perturbed_mass_drop (m-1) (by omega : 3 ≤ n) ((c : ℤ)+1)
    rw [even_strict_reflection_mass m hm hn c] at hs
    have hnt : ¬reflectionBoard (m-1) ((c : ℤ)+1) (2 : Fin n)=(n : ℤ)-(m-1 : ℕ)-1 :=
      fun ht => hc (even_strict_top_phase m hm hn c ht)
    rw [ite_eq_right hnt,sub_zero] at hs
    change (n : ℤ)*(((c : ℤ)+m)%2) ≤ ∑ i,evenStrictBase m c i at hs
    rw [hz] at hs
    have hn' : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
    have hmod : ((c : ℤ)+m)%2=0 := by
      have hr := Int.emod_nonneg ((c : ℤ)+m) (by decide : (2 : ℤ) ≠ 0)
      nlinarith
    have hcmod : ((c.val+m)%2 : ℕ)=0 := by
      have hcast : (((c.val+m)%2 : ℕ) : ℤ)=0 := by
        simpa only [Int.natCast_emod,Nat.cast_add,Nat.cast_ofNat] using hmod
      omega
    exact hcmod
