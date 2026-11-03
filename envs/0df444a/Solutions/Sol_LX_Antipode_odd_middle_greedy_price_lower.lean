-- Prove2me | solution 1 for LX.Antipode.odd_middle_greedy_price_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:17:58.50391+00:00
-- url     : https://prove2.me/submissions/22f00ba9-2063-4e50-9df0-f39d1e8c0b25

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_ColoredReflectionLower
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_OddMiddleInversions
import Definitions.Def_LX_OddSingleRaise
import Definitions.Def_LX_PhaseMinimumRescue
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoColorPairs
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_AffineScan_ScanTrace_paid_token_bound
import Theorems.Thm_LX_AffineScan_displacement_rotation_lower
import Theorems.Thm_LX_AffineScan_exists_depth_extreme
import Theorems.Thm_LX_AffineScan_exists_reflection_winding
import Theorems.Thm_LX_AffineScan_raise_coordinate_inversions
import Theorems.Thm_LX_AffineScan_reflection_opposite_pairs
import Theorems.Thm_LX_AffineScan_reflection_perturbation_pairs
import Theorems.Thm_LX_AffineScan_reflection_token_bound
import Theorems.Thm_LX_Antipode_odd_middle_minimum_pair
import Theorems.Thm_LX_Antipode_odd_middle_opposite_count
import Theorems.Thm_LX_Antipode_odd_no_mid_top_mass
import Theorems.Thm_LX_Antipode_odd_rank_inversions
import Theorems.Thm_LX_CenteredLift_balanced_single_raise
import Theorems.Thm_LX_CenteredLift_odd_perturbed_board_mass
import Theorems.Thm_LX_CenteredLift_raised_source_lift
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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]





end LX.AffineScan

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem odd_opposite_pairs_count (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (χ : Fin n → Bool) :
    oppositeColorInversions (oddRank m hm hn) χ=
      (Finset.univ.filter fun j : Fin n => 2 < j.val ∧ j.val ≤ m+1 ∧ χ 2 ≠ χ j).card := by
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hp (i j : Fin n) :
      (i < j ∧ oddRank m hm hn j < oddRank m hm hn i) ↔ i=2 ∧ 2 < j.val ∧ j.val ≤ m+1 := by
    have hea : i=2 ↔ i.val=2 := by rw [Fin.ext_iff,hv2]
    rw [hea]
    change (i.val < j.val ∧ oddRankValue m j.val < oddRankValue m i.val) ↔
      i.val=2 ∧ 2 < j.val ∧ j.val ≤ m+1
    unfold oddRankValue
    split_ifs <;> omega
  unfold oppositeColorInversions
  simp_rw [← and_assoc,hp]
  rw [Finset.sum_comm]
  simp only [and_assoc,ite_and,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [← ite_and,Finset.sum_boole]
  rfl

theorem odd_colored_inversions_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (d : Fin n → ℤ) (C : ℤ) (k : Fin n → ℤ)
    (hF : ∀ i,targets d i=C-(oddRank m hm hn i : ℤ)+(n : ℤ)*k i) :
    m^2+2*(Finset.univ.filter fun j : Fin n =>
      2 < j.val ∧ j.val ≤ m+1 ∧ decide (k 2 % 2=0) ≠ decide (k j % 2=0)).card ≤
        inversions d+(m-1) := by
  have hh := reflection_opposite_pairs d (oddRank m hm hn) C k hF
  rw [odd_rank_inversions m hm hn,odd_opposite_pairs_count m hm hn] at hh
  have hp := odd_same_color_pairs_lower (fun i => decide (k i % 2=0)) m hn
  omega


end LX.Antipode

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]









/-- A lower displacement bound controls every token's backward exchanges. -/
theorem backward_depth_le_strip {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (h : ℤ) (hlo : ∀ i, -h ≤ d i) (i : Fin n) :
    (backwardDepth d i : ℤ) ≤ h := by
  obtain ⟨a,hmax,he⟩ := exists_depth_extreme hd
  have hh : (backwardDepth d i : ℤ) ≤ backwardDepth d a := by exact_mod_cast hmax i
  have := hlo a
  omega




end LX.AffineScan

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

/-- Complete restriction of a putative cheaper word of the odd candidate
to n phases and at most n+1 explicitly described lifts per phase. -/
theorem odd_unpaid_single_raise (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-m+1) :
    d=oddBase m hm hn c ∨ ∃ a,d=raiseAt (oddBase m hm hn c) a :=
  odd_lift_single_raise m hm hn c hd (odd_unpaid_lower_strip m hm hn hd hg hu)



end LX.Antipode

end

section
namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem perturbed_board_winding (h : ℕ) (C : ℤ) (ρ : State n) (i : Fin n) :
    LX.AffineScan.targets (perturbedBoard h C ρ) i=C-(ρ i : ℤ)+(n : ℤ)*winding h C ρ i := by
  have he := Int.ediv_mul_add_emod (C-(ρ i : ℤ)-(i : ℤ)+h) (n : ℤ)
  unfold LX.AffineScan.targets perturbedBoard center winding
  nlinarith

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]









theorem odd_middle_base_inversions (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) :
    m*(m-1)+1+2*((m-c.val+1)/2) ≤ inversions (oddBase m hm hn c) := by
  have hF (i : Fin n) : targets (oddBase m hm hn c) i=
      ((c : ℤ)+1)-(oddRank m hm hn i : ℤ)+(n : ℤ)*oddBaseWinding m hm hn c i :=
    perturbed_board_winding m ((c : ℤ)+1) (oddRank m hm hn) i
  have hI := odd_colored_inversions_lower m hm hn (oddBase m hm hn c) ((c : ℤ)+1)
    (oddBaseWinding m hm hn c) hF
  have hK := odd_middle_opposite_count m hm hn c hc hcl
  have hm1 : m-1+1=m := by omega
  nlinarith


end LX.Antipode

end

section
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem odd_middle_no_top (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1) (hpar : (c.val+m)%2=1)
    (j : Fin n) (hj : 3 ≤ j.val) (hjl : j.val ≤ m+1) :
    reflectionBoard m ((c : ℤ)+1) j ≠ (m : ℤ) := by
  intro he
  let z : ℤ := (c : ℤ)+1-2*(j : ℤ)
  change center (n := n) m z=(m : ℤ) at he
  have hzhi : z < (m : ℤ) := by dsimp [z]; omega
  have hzlo : 1-2*(m : ℤ) ≤ z := by dsimp [z]; omega
  by_cases hz : -(m : ℤ) ≤ z
  · have hh := center_eq_of_translate (n := n) m z z 0 (by ring)
      ⟨hz,by omega⟩
    rw [hh] at he
    omega
  · have hh := center_eq_of_translate (n := n) m z (z+n) (-1) (by ring)
      ⟨by omega,by omega⟩
    rw [hh] at he
    dsimp only [z] at he
    omega

theorem odd_middle_raised_parity (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c a : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    (hd : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a)) :
    (c.val+m)%2=0 := by
  by_contra hnot
  have hpar : (c.val+m)%2=1 := by omega
  have hmass := odd_no_mid_top_mass m hm hn c (odd_middle_no_top m hm hn c hc hcl hpar)
  have hs : (∑ i : Fin n,raiseAt (oddBase m hm hn c) a i)=
      (∑ i : Fin n,oddBase m hm hn c i)+(n : ℤ) := by simp [raiseAt,Finset.sum_add_distrib]
  have hz := hd.1
  rw [hs] at hz
  have := NeZero.pos n
  omega


end LX.Antipode

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem reflection_head_token_bound (hn : 2 ≤ n) {p : State n} {c : Fin n} {d : Fin n → ℤ}
    (hd : IsLift p (c : ℤ) d) {g : List Letter} (hg : ScanTrace d g)
    (hp : p.symm 0=1) :
    ((n : ℤ)-1)*(1-d 0) ≤ (paidRotations c g : ℤ) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have h10 : (1 : Fin n) ≠ 0 := by intro hh; have := congrArg Fin.val hh; simp only [hv1,Fin.val_zero] at this; omega
  have hqval : ((-(1 : Fin n)).val : ℤ)=(n : ℤ)-1 := by
    rw [Fin.val_neg,ite_eq_right h10,hv1]
    omega
  have ht := hg.paid_token_bound hn hd 0
  rw [hp,hqval] at ht
  simp only [targets,Fin.val_zero,Nat.cast_zero,Nat.zero_sub,mul_zero,zero_add,zero_sub] at ht
  nlinarith

end LX.AffineScan

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]




end LX.Antipode

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem raise_minimum_apply (d : Fin n → ℤ) (a i : Fin n) :
    raiseMinimum d a i=d i-1+if i=a then (n : ℤ) else 0 := by
  have hn : 1 ≤ n := NeZero.pos n
  unfold raiseMinimum phaseShift
  simp only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hn,Nat.cast_one,Finset.mem_erase,Finset.mem_univ,and_true]
  by_cases hi : i=a <;> simp [hi] <;> ring




end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]









theorem raise_coordinate_inversions_lower {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) (hw : ∀ i j,d i-d j < (n : ℤ))
    (h : ℕ) (hlo : ∀ i,-(h : ℤ) ≤ d i) :
    (inversions d : ℤ)+(n : ℤ)-1-2*h ≤ inversions (raiseMinimum d a) := by
  have he := raise_coordinate_inversions hd a hw
  have hb := backward_depth_le_strip hd (h : ℤ) hlo a
  omega



end LX.AffineScan

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem inversions_add_constant (d : Fin n → ℤ) (t : ℤ) :
    inversions (fun i => d i+t)=inversions d := by
  unfold inversions LX.Core.LiftedModel.inversionCount
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : targets (fun i => d i+t) j-targets (fun i => d i+t) i=targets d j-targets d i := by
    unfold targets
    ring
  rw [he]

end LX.AffineScan

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem raise_source_eq (e : Fin n → ℤ) (a : Fin n) :
    raiseMinimum (fun i => e i+1) a=raiseAt e a := by
  funext i
  rw [raise_minimum_apply]
  simp only [raiseAt,Nat.cast_ite,Nat.cast_zero]
  ring

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem odd_raised_base_inversions (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c a : Fin n) (hd : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a)) :
    inversions (oddBase m hm hn c)+2 ≤ inversions (raiseAt (oddBase m hm hn c) a) := by
  have hsource := raised_source_lift a hd
  have hw : ∀ i j : Fin n,(oddBase m hm hn c i+1)-(oddBase m hm hn c j+1) < (n : ℤ) := by
    intro i j
    have hi := odd_base_bounds m hm hn c i
    have hj := odd_base_bounds m hm hn c j
    omega
  have hlo : ∀ i : Fin n,-((m-1 : ℕ) : ℤ) ≤ oddBase m hm hn c i+1 := by
    intro i
    have hh := odd_base_bounds m hm hn c i
    omega
  have hh := raise_coordinate_inversions_lower hsource a hw (m-1) hlo
  rw [raise_source_eq,inversions_add_constant] at hh
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hgoal : (inversions (oddBase m hm hn c) : ℤ)+2 ≤
      inversions (raiseAt (oddBase m hm hn c) a) := by omega
  exact_mod_cast hgoal

theorem odd_middle_raised_inversions (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (c a : Fin n) (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    (hd : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a)) :
    m*(m-1)+1+2*((m-c.val+1)/2)+2 ≤ inversions (raiseAt (oddBase m hm hn c) a) := by
  have hbase := odd_middle_base_inversions m hm hn c hc hcl
  have hraise := odd_raised_base_inversions m hm hn c a hd
  omega



end LX.Antipode

end

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every lift in the middle phase interval meets the sharp odd price.
The argument includes both unraised and single-raised profiles. -/
theorem solution (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} (hc : 2 ≤ c.val) (hcl : c.val ≤ m+1)
    {d : Fin n → ℤ} (hd : IsLift (odd m hm hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-m+1 := by omega
  let ε : ℕ := (c.val+m)%2
  have hε : ε ≤ 1 := by dsimp [ε]; omega
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hK : (2 : ℤ)*(((m-c.val+1)/2 : ℕ) : ℤ)=(m : ℤ)-(c : ℤ)+ε := by dsimp [ε]; omega
  let ρ : State n := oddRank m hm hn
  have hp (i : Fin n) : (odd m hm hn).symm i=1-ρ i := rfl
  obtain ⟨j,t,hjlo,hjhi,hjt,hjtwice,htloc,hjbase,htbase⟩ := odd_middle_minimum_pair m hm hn c hc hcl
  change 2*j.val+ε=c.val+m+2 at hjtwice
  change oddBase m hm hn c j=(ε : ℤ)-m at hjbase
  change oddBase m hm hn c t=(ε : ℤ)-m at htbase
  have hjtwice' : 2*(j : ℤ)+ε=(c : ℤ)+m+2 := by exact_mod_cast hjtwice
  have hmid (hdj : d j=(ε : ℤ)-m) :
      2*(m : ℤ)^2+(c : ℤ)-m-1-(n : ℤ)*ε ≤ (paidRotations c g : ℤ) := by
    have hrj : (ρ j).val=j.val-1 := by
      change oddRankValue m j.val=j.val-1
      simp only [oddRankValue,ite_eq_right (by omega : j.val ≠ 2),
        ite_eq_left (show 3 ≤ j.val ∧ j.val ≤ m+1 from ⟨hjlo,hjhi⟩)]
    have ht := reflection_token_bound (by omega : 2 ≤ n) hd hg ρ hp j (by omega)
      (by rw [hrj]; omega)
    have hrj' : (ρ j : ℤ)=(j : ℤ)-1 := by rw [hrj]; omega
    rw [hrj',hdj] at ht
    rw [hn'] at ht ⊢
    nlinarith only [ht,hjtwice']
  have htail (hdt : d t=(ε : ℤ)-m) :
      2*(m : ℤ)^2+m+(c : ℤ)-(n : ℤ)*ε ≤ (paidRotations c g : ℤ) := by
    rcases htloc with ⟨ht0,hkn⟩ | ⟨htlo,htval⟩
    · subst t
      have hr0 : ρ 0=0 := by apply Fin.ext; simp [ρ,oddRank,oddRankValue]
      have hq0 : (odd m hm hn).symm 0=1 := by rw [hp,hr0,sub_zero]
      have ht := reflection_head_token_bound (by omega : 2 ≤ n) hd hg hq0
      rw [hdt] at ht
      rw [hn'] at ht ⊢
      have hcm : (c : ℤ)=(m : ℤ)+ε := by omega
      rw [hcm]
      nlinarith
    · have hrt : ρ t=t := by
        apply Fin.ext
        change oddRankValue m t.val=t.val
        simp only [oddRankValue,ite_eq_right (by omega : t.val ≠ 2),
          ite_eq_right (by omega : ¬(3 ≤ t.val ∧ t.val ≤ m+1))]
      have ht := reflection_token_bound (by omega : 2 ≤ n) hd hg ρ hp t (by omega)
        (by rw [hrt]; omega)
      rw [hrt,hdt] at ht
      rw [hn'] at ht ⊢
      have htval' : (t : ℤ)=(j : ℤ)+m := by exact_mod_cast htval
      rw [htval'] at ht
      nlinarith
  have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-m+1 : ℕ) : ℤ) := by exact_mod_cast hu
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : m ≤ 3*m^2)] at hu'
  push_cast at hu'
  rcases odd_unpaid_single_raise m hm hn hd hg hu with he | ⟨a,ha⟩
  · have hI : m*(m-1)+1+2*((m-c.val+1)/2) ≤ inversions d := by
      rw [he]
      exact odd_middle_base_inversions m hm hn c hc hcl
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ)+1+2*(((m-c.val+1)/2 : ℕ) : ℤ) ≤ (inversions d : ℤ) := by
      exact_mod_cast hI
    rw [hm1,hK] at hI'
    have hdt : d t=(ε : ℤ)-m := by rw [he]; exact htbase
    have hR := htail hdt
    rw [hn'] at hR
    have hprod := mul_nonneg (Nat.cast_nonneg m : (0 : ℤ) ≤ m)
      (show (0 : ℤ) ≤ 1-(ε : ℤ) by omega)
    nlinarith only [hI',hR,hu',hprod]
  · have hda : IsLift (odd m hm hn) (c : ℤ) (raiseAt (oddBase m hm hn c) a) := by rwa [ha] at hd
    have hε0 : ε=0 := odd_middle_raised_parity m hm hn c a hc hcl hda
    have hI : m*(m-1)+1+2*((m-c.val+1)/2)+2 ≤ inversions d := by
      rw [ha]
      exact odd_middle_raised_inversions m hm hn c a hc hcl hda
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ)+1+2*(((m-c.val+1)/2 : ℕ) : ℤ)+2 ≤ (inversions d : ℤ) := by
      exact_mod_cast hI
    rw [hm1,hK,hε0,Nat.cast_zero,add_zero] at hI'
    have hR : 2*(m : ℤ)^2+(c : ℤ)-m-1 ≤ (paidRotations c g : ℤ) := by
      by_cases hat : a=t
      · have hdj : d j=(ε : ℤ)-m := by
          rw [ha]
          simp only [raiseAt,ite_eq_right (show j ≠ a by rw [hat]; exact hjt),Nat.cast_zero,add_zero]
          exact hjbase
        have hh := hmid hdj
        simpa only [hε0,Nat.cast_zero,mul_zero,sub_zero] using hh
      · have hdt : d t=(ε : ℤ)-m := by
          rw [ha]
          simp only [raiseAt,ite_eq_right (Ne.symm hat),Nat.cast_zero,add_zero]
          exact htbase
        have hh := htail hdt
        rw [hε0,Nat.cast_zero,mul_zero,sub_zero] at hh
        nlinarith
    nlinarith only [hI',hR,hu']
