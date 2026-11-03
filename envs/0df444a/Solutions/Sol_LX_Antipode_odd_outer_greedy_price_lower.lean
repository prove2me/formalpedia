-- Prove2me | solution 1 for LX.Antipode.odd_outer_greedy_price_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:18:07.511385+00:00
-- url     : https://prove2.me/submissions/9ab6c5e1-fc94-4878-b968-70044bb71dc4

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
import Definitions.Def_LX_AntipodeCandidates
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_OddOuterMass
import Definitions.Def_LX_OddSingleRaise
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoColorPairs
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_AffineScan_displacement_rotation_lower
import Theorems.Thm_LX_AffineScan_exists_reflection_winding
import Theorems.Thm_LX_AffineScan_reflection_perturbation_pairs
import Theorems.Thm_LX_AffineScan_reflection_token_bound
import Theorems.Thm_LX_Antipode_odd_mid_top_equations
import Theorems.Thm_LX_Antipode_odd_no_mid_top_mass
import Theorems.Thm_LX_Antipode_odd_outer_special_wrap
import Theorems.Thm_LX_Antipode_odd_rank_inversions
import Theorems.Thm_LX_Antipode_odd_special_wrap_mass
import Theorems.Thm_LX_CenteredLift_balanced_single_raise
import Theorems.Thm_LX_CenteredLift_odd_perturbed_board_mass
import Theorems.Thm_LX_CenteredLift_odd_reflection_residue_bijective
import Theorems.Thm_LX_same_color_pair_count

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



theorem ScanTrace.run_zero {d : Fin n → ℤ} {w : List Letter} (ht : ScanTrace d w) :
    ∀ i, run w d i = 0 := by
  induction ht with
  | done hz => exact hz
  | left _ _ _ ih => exact ih
  | swap _ _ ih => exact ih















end LX.AffineScan

end

section
namespace LX
open scoped BigOperators
variable {n : ℕ}





theorem color_count_sum (χ : Fin n → Bool) : colorCount χ true+colorCount χ false=n := by
  have hp (i : Fin n) : (if χ i=true then 1 else 0)+(if χ i=false then 1 else 0)=(1 : ℕ) := by
    cases χ i <;> simp
  have hs := congrArg (fun f : Fin n → ℕ => ∑ i,f i) (funext hp)
  convert hs using 1 <;>
    simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one,colorCount] <;> rfl





theorem odd_same_color_pairs_lower (χ : Fin n → Bool) (m : ℕ) (hn : n=2*m+1) :
    m^2 ≤ sameColorPairs χ := by
  have hs := color_count_sum χ
  have hp := same_color_pair_count χ
  have hs' : (colorCount χ true : ℤ)+(colorCount χ false : ℤ)=2*m+1 := by omega
  have hp' : 2*(sameColorPairs χ : ℤ)+(n : ℤ)=
      (colorCount χ true : ℤ)^2+(colorCount χ false : ℤ)^2 := by exact_mod_cast hp
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hsq := sq_nonneg ((colorCount χ true : ℤ)-(colorCount χ false : ℤ))
  have he : (m : ℤ)^2 ≤ (sameColorPairs χ : ℤ) := by nlinarith
  exact_mod_cast he



end LX

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





theorem odd_reflection_lift_inversions_lower (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ) (m : ℕ) (hn : n=2*m+1)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    m^2 ≤ inversions d+LX.Core.FiniteCuts.inversionNumber ρ :=
  (odd_same_color_pairs_lower _ m hn).trans (reflection_perturbation_pairs d ρ C k hF)





theorem odd_reflection_lift_lower {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (ρ : State n)
    (hp : ∀ i,p.symm i=1-ρ i) (m : ℕ) (hn : n=2*m+1) :
    m^2 ≤ inversions d+LX.Core.FiniteCuts.inversionNumber ρ := by
  obtain ⟨k,hk⟩ := exists_reflection_winding hd ρ hp
  exact odd_reflection_lift_inversions_lower d ρ (c+1) k m hn hk





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

















theorem odd_lift_inversions_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : ℤ} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift (odd m hm hn) c d) :
    m^2 ≤ inversions d+(m-1) := by
  have hp (i : Fin n) : (odd m hm hn).symm i=1-(oddRank m hm hn) i := rfl
  have hh := odd_reflection_lift_lower hd (oddRank m hm hn) hp m hn
  rwa [odd_rank_inversions m hm hn] at hh



end LX.Antipode

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



end LX.AffineScan

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]



theorem odd_large_height_paid (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) (i : Fin n) (hi : d i < -(m : ℤ)) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  have hI := odd_lift_inversions_lower m hm hn hd
  have hL := displacement_rotation_lower (by omega : 2 ≤ n) d g hg.run_zero m i (by omega)
  have hpad : g.count .l ≤ paidRotations c g := by simp only [paidRotations]; omega
  have hn1 : n-1+1=n := by omega
  have hm1 : m-1+1=m := by omega
  have hsub := Nat.sub_add_cancel (show m ≤ 3*m^2 by nlinarith)
  nlinarith



theorem odd_unpaid_lower_strip (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-m+1) :
    ∀ i,-(m : ℤ) ≤ d i := by
  intro i
  by_contra hi
  have hh := odd_large_height_paid m hm hn hd hg i (by omega)
  omega



end LX.Antipode

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














end LX.CenteredLift

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





theorem reflection_board_eq_val (m : ℕ) (C : ℤ) (i : Fin n) :
    reflectionBoard m C i=(reflectionResidue m C i : ℤ)-m := by
  have he : reflectionResidue m C i=(((C-2*(i : ℤ)+m : ℤ)) : Fin n) := by
    simp only [reflectionResidue,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,
      Int.cast_natCast,Fin.cast_val_eq_self]
    ring
  rw [he]
  have hr := Int.emod_nonneg (C-2*(i : ℤ)+m) (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)
  simp only [reflectionBoard,center,Fin.val_intCast,Int.toNat_of_nonneg hr]



theorem odd_reflection_board_injective (m : ℕ) (hn : n=2*m+1) (C : ℤ) :
    Function.Injective (reflectionBoard (n := n) m C) := by
  intro i j hij
  rw [reflection_board_eq_val,reflection_board_eq_val] at hij
  apply (odd_reflection_residue_bijective m hn C).1
  apply Fin.ext
  omega






end LX.CenteredLift

end

section
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem center_eq_of_translate (m : ℕ) (z v k : ℤ)
    (hz : z=v+(n : ℤ)*k) (hv : -(m : ℤ) ≤ v ∧ v < (n : ℤ)-m) :
    center (n := n) m z=v := by
  have he : z+m=(v+m)+k*(n : ℤ) := by rw [hz]; ring
  unfold center
  rw [he,Int.add_emod]
  simp only [Int.mul_emod_left,add_zero,Int.emod_eq_of_lt (by omega : 0 ≤ v+m)
    (by omega : v+m < (n : ℤ))]
  omega

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]









end LX.Antipode

end

section
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]



theorem odd_base_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n) :
    -(n : ℤ) ≤ ∑ i,oddBase m hm hn c i := by
  apply odd_perturbed_board_mass m hn ((c : ℤ)+1) (oddRank m hm hn)
  intro i
  change (i : ℤ)-(oddRankValue m i.val : ℤ) ≤ 1
  unfold oddRankValue
  split_ifs <;> omega

theorem odd_base_bounds (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c i : Fin n) :
    -(m : ℤ) ≤ oddBase m hm hn c i ∧ oddBase m hm hn c i < (n : ℤ)-m :=
  center_bounds m _

theorem odd_base_residue (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift (odd m hm hn) (c : ℤ) d) (i : Fin n) :
    (d i : Fin n)=(oddBase m hm hn c i : Fin n) := by
  have hh := LX.Core.AffineLift.lift_residue hd i
  simp only [odd,Equiv.symm_symm,Equiv.Perm.mul_apply,LX.Core.WordReflection.reflection_apply,
    Int.cast_natCast,Fin.cast_val_eq_self] at hh
  change (d i : Fin n)=(center (n := n) m (((c : ℤ)+1)-(oddRank m hm hn i : ℤ)-(i : ℤ)) : Fin n)
  rw [center_cast]
  simp only [Int.cast_sub,Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
  linear_combination hh

/-- All balanced lifts in the surviving lower strip, at every phase,
are a fixed representative or a single-coordinate raise. -/
theorem odd_lift_single_raise (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    d=oddBase m hm hn c ∨ ∃ a,d=raiseAt (oddBase m hm hn c) a := by
  exact balanced_single_raise m d (oddBase m hm hn c) hd.1 hlo
    (odd_base_bounds m hm hn c) (odd_base_residue m hm hn c hd) (odd_base_mass m hm hn c)





end LX.Antipode

end

section
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem odd_mid_top_card (m : ℕ) (hn : n=2*m+1) (c : Fin n) : (oddMidTop m c).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply odd_reflection_board_injective m hn ((c : ℤ)+1)
  exact (Finset.mem_filter.mp hi).2.2.2.trans (Finset.mem_filter.mp hj).2.2.2.symm



theorem odd_special_wrap_mass_nonnegative (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hw : reflectionBoard m ((c : ℤ)+1) (2 : Fin n) ≤ -2) :
    0 ≤ ∑ i,oddBase m hm hn c i := by
  have hs := odd_special_wrap_mass m hm hn c hw
  have hc := odd_mid_top_card m hn c
  have hc' : ((oddMidTop m c).card : ℤ) ≤ 1 := by exact_mod_cast hc
  have hh := mul_le_mul_of_nonneg_left hc' (show (0 : ℤ) ≤ n by positivity)
  nlinarith





theorem odd_outer_base_nonnegative (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : c.val ≤ 1 ∨ m+3 ≤ c.val) : 0 ≤ ∑ i,oddBase m (by omega) hn c i := by
  by_cases he : c.val=m+3
  · apply odd_no_mid_top_mass
    intro j hj hjl ht
    have hh := odd_mid_top_equations m (by omega) hn c j hj hjl ht
    omega
  · exact odd_special_wrap_mass_nonnegative m (by omega) hn c
      (odd_outer_special_wrap m hm hn c (by omega))


end LX.Antipode

end

section
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem odd_outer_bad_mass (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : (c.val ≤ 1 ∧ (c.val+m)%2=1) ∨ (m+3 ≤ c.val ∧ (c.val+m)%2=0)) :
    (n : ℤ) ≤ ∑ i,oddBase m (by omega) hn c i := by
  have hw := odd_outer_special_wrap m hm hn c (by rcases hc with hc | hc <;> omega)
  have hs := odd_special_wrap_mass m (by omega) hn c hw
  have hS : oddMidTop m c=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have ht := (Finset.mem_filter.mp hj).2
    have he := odd_mid_top_equations m (by omega) hn c j ht.1 ht.2.1 ht.2.2
    rcases hc with hc | hc <;> omega
  simpa only [hS,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero] using hs

theorem odd_outer_lift_unique (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : c.val ≤ 1 ∨ m+3 ≤ c.val) {d : Fin n → ℤ}
    (hd : IsLift (odd m (by omega) hn) (c : ℤ) d) (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    d=oddBase m (by omega) hn c := by
  rcases odd_lift_single_raise m (by omega) hn c hd hlo with he | ⟨a,ha⟩
  · exact he
  · have hmass := odd_outer_base_nonnegative m hm hn c hc
    have hz := hd.1
    rw [ha] at hz
    have hs : (∑ i : Fin n,raiseAt (oddBase m (by omega) hn c) a i)=
        (∑ i : Fin n,oddBase m (by omega) hn c i)+(n : ℤ) := by simp [raiseAt,Finset.sum_add_distrib]
    rw [hs] at hz
    have := NeZero.pos n
    omega

theorem odd_outer_phase_parity (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : c.val ≤ 1 ∨ m+3 ≤ c.val) {d : Fin n → ℤ}
    (hd : IsLift (odd m (by omega) hn) (c : ℤ) d) (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    (c.val ≤ 1 ∧ (c.val+m)%2=0) ∨ (m+3 ≤ c.val ∧ (c.val+m)%2=1) := by
  have he := odd_outer_lift_unique m hm hn c hc hd hlo
  have hz := hd.1
  rw [he] at hz
  rcases hc with hc | hc
  · left
    refine ⟨hc,?_⟩
    by_contra hnot
    have hs := odd_outer_bad_mass m hm hn c (Or.inl ⟨hc,by omega⟩)
    rw [hz] at hs
    have := NeZero.pos n
    omega
  · right
    refine ⟨hc,?_⟩
    by_contra hnot
    have hs := odd_outer_bad_mass m hm hn c (Or.inr ⟨hc,by omega⟩)
    rw [hz] at hs
    have := NeZero.pos n
    omega

theorem odd_outer_minimum_location (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) (c : Fin n)
    (hc : (c.val ≤ 1 ∧ (c.val+m)%2=0) ∨ (m+3 ≤ c.val ∧ (c.val+m)%2=1)) :
    ∃ t : Fin n,m+2 ≤ t.val ∧ oddBase m (by omega) hn c t= -(m : ℤ) := by
  have hclt := c.isLt
  rcases hc with ⟨hc,hpar⟩ | ⟨hc,hpar⟩
  · let k : ℕ := (c.val+3*m+2)/2
    have hk : 2*k=c.val+3*m+2 := by dsimp [k]; omega
    have hklo : m+2 ≤ k := by omega
    have hkhi : k < n := by omega
    let t : Fin n := ⟨k,hkhi⟩
    have hr : (oddRank m (by omega) hn t).val=k := by
      change oddRankValue m k=k
      simp only [oddRankValue,ite_eq_right (by omega : k ≠ 2),
        ite_eq_right (by omega : ¬(3 ≤ k ∧ k ≤ m+1))]
    refine ⟨t,hklo,?_⟩
    unfold oddBase perturbedBoard
    rw [hr]
    change center (n := n) m ((c : ℤ)+1-(k : ℤ)-(k : ℤ))= -(m : ℤ)
    apply center_eq_of_translate m _ _ (-1)
    · omega
    · constructor <;> omega
  · let k : ℕ := (c.val+m+1)/2
    have hk : 2*k=c.val+m+1 := by dsimp [k]; omega
    have hklo : m+2 ≤ k := by omega
    have hkhi : k < n := by omega
    let t : Fin n := ⟨k,hkhi⟩
    have hr : (oddRank m (by omega) hn t).val=k := by
      change oddRankValue m k=k
      simp only [oddRankValue,ite_eq_right (by omega : k ≠ 2),
        ite_eq_right (by omega : ¬(3 ≤ k ∧ k ≤ m+1))]
    refine ⟨t,hklo,?_⟩
    unfold oddBase perturbedBoard
    rw [hr]
    change center (n := n) m ((c : ℤ)+1-(k : ℤ)-(k : ℤ))= -(m : ℤ)
    apply center_eq_of_translate m _ _ 0
    · omega
    · constructor <;> omega




end LX.Antipode

end

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem solution (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1)
    {c : Fin n} (hc : c.val ≤ 1 ∨ m+3 ≤ c.val)
    {d : Fin n → ℤ} (hd : IsLift (odd m (by omega) hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-m+1 := by omega
  have hlo := odd_unpaid_lower_strip m (by omega) hn hd hg hu
  have he := odd_outer_lift_unique m hm hn c hc hd hlo
  have hpar := odd_outer_phase_parity m hm hn c hc hd hlo
  obtain ⟨t,htlo,htvalue⟩ := odd_outer_minimum_location m hm hn c hpar
  have hdt : d t= -(m : ℤ) := by rw [he]; exact htvalue
  let ρ : State n := oddRank m (by omega) hn
  have hp (i : Fin n) : (odd m (by omega) hn).symm i=1-ρ i := rfl
  have hrt : ρ t=t := by
    apply Fin.ext
    change oddRankValue m t.val=t.val
    simp only [oddRankValue,ite_eq_right (by omega : t.val ≠ 2),
      ite_eq_right (by omega : ¬(3 ≤ t.val ∧ t.val ≤ m+1))]
  have hR := reflection_token_bound (by omega : 2 ≤ n) hd hg ρ hp t (by omega) (by rw [hrt]; omega)
  rw [hrt,hdt] at hR
  have hI := odd_lift_inversions_lower m (by omega) hn hd
  have hI' : (m : ℤ)^2 ≤ (inversions d : ℤ)+((m-1 : ℕ) : ℤ) := by exact_mod_cast hI
  have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-m+1 : ℕ) : ℤ) := by exact_mod_cast hu
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : m ≤ 3*m^2)] at hu'
  push_cast at hu'
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have ht' : (m : ℤ)+2 ≤ t := by omega
  rw [hn'] at hR
  rw [hm1] at hI'
  nlinarith only [hR,hI',hu',ht']
