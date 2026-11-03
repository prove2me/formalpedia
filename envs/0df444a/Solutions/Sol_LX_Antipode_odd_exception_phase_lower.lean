-- Prove2me | solution 1 for LX.Antipode.odd_exception_phase_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:21:43.347741+00:00
-- url     : https://prove2.me/submissions/5add2d54-38c4-46f5-89ea-c6dbe10cac2a

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
import Definitions.Def_LX_ExceptionalPrefixDelay
import Definitions.Def_LX_ExceptionalPriceLower
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FiniteWindowInversions
import Definitions.Def_LX_Graph
import Definitions.Def_LX_GreedyScan
import Definitions.Def_LX_OddCenteredMass
import Definitions.Def_LX_OddSingleRaise
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoColorPairs
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_AffineScan_displacement_rotation_lower
import Theorems.Thm_LX_AffineScan_exists_reflection_winding
import Theorems.Thm_LX_AffineScan_interval_depth_lower
import Theorems.Thm_LX_AffineScan_odd_exception_paid_rotation_lower
import Theorems.Thm_LX_AffineScan_reflection_perturbation_pairs
import Theorems.Thm_LX_AffineScan_sum_depth_eq_inversions
import Theorems.Thm_LX_AffineScan_tail_head_depth_lower
import Theorems.Thm_LX_Antipode_odd_rank_inversions
import Theorems.Thm_LX_CenteredLift_balanced_single_raise
import Theorems.Thm_LX_CenteredLift_odd_perturbed_board_mass
import Theorems.Thm_LX_Core_AffineLift_crossing_row_sum
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
namespace LX.FinitePairReduction
end LX.FinitePairReduction
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



/-- Net displacement plus incoming crossings is exactly the outgoing crossing count. -/
theorem displacement_add_depth {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (i : Fin n) :
    d i+(backwardDepth d i : ℤ)=
      ∑ j, ((LX.Core.AffineLift.crossing d i j).toNat : ℤ) := by
  rw [← LX.Core.AffineLift.crossing_row_sum hd i]
  simp only [backwardDepth,Nat.cast_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]



theorem neg_displacement_le_depth {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LX.Core.AffineLift.IsLift p c d) (i : Fin n) :
    -d i ≤ (backwardDepth d i : ℤ) := by
  have hh := displacement_add_depth hd i
  have hs : (0 : ℤ) ≤ ∑ j : Fin n,((LX.Core.AffineLift.crossing d i j).toNat : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  omega



















end LX.AffineScan

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
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]











theorem odd_exception_depth_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (oddException m))
    (i : Fin n) : oddDepthLower m i.val ≤ backwardDepth (oddException m) i := by
  have hil := i.isLt
  unfold oddDepthLower
  split_ifs with hi0 hi1 hi2 hiM
  · have hi : i=0 := Fin.ext hi0
    subst i
    have hh := tail_head_depth_lower (oddException (n := n) m) (⟨m+2,by omega⟩ : Fin n) (by
      intro j hj
      have hjl := j.isLt
      have hjp : m+2 ≤ j.val := hj
      simp only [targets,oddException,Fin.val_zero,Nat.cast_zero,ite_true,zero_add]
      rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : j.val ≠ 1),
        ite_eq_right (by omega : j.val ≠ 2),ite_eq_right (by omega : ¬j.val ≤ m+1)]
      omega)
    simpa only [show n-(m+2)=m-1 by omega] using hh
  · have hh := neg_displacement_le_depth hd i
    simp only [oddException,ite_eq_right hi0,ite_eq_left hi1] at hh
    omega
  · exact Nat.zero_le _
  · apply interval_depth_lower (oddException m) (⟨3,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : 3 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,oddException,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2,
      ite_eq_left hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : j.val ≠ 1),
      ite_eq_right (by omega : j.val ≠ 2),ite_eq_left (by omega : j.val ≤ m+1)]
    omega
  · apply interval_depth_lower (oddException m) (⟨m+2,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : m+2 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,oddException,ite_eq_right hi0,ite_eq_right hi1,ite_eq_right hi2,
      ite_eq_right hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : j.val ≠ 1),
      ite_eq_right (by omega : j.val ≠ 2),ite_eq_right (by omega : ¬j.val ≤ m+1)]
    omega



omit [NeZero n] in
theorem odd_depth_lower_sum (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    ∑ i : Fin n,oddDepthLower m i.val=m*(m-1)+1 := by
  rw [Fin.sum_univ_eq_sum_range,show n=3+(m-1)+(m-1) by omega,
    Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range 3,oddDepthLower m k)=(m-1)+m := by
    norm_num [Finset.sum_range_succ,oddDepthLower]
  have hmid : (∑ k ∈ Finset.range (m-1),oddDepthLower m (3+k))=
      ∑ k ∈ Finset.range (m-1),k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    unfold oddDepthLower
    split_ifs <;> omega
  have htail : (∑ k ∈ Finset.range (m-1),oddDepthLower m (3+(m-1)+k))=
      ∑ k ∈ Finset.range (m-1),k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold oddDepthLower
    split_ifs <;> omega
  rw [hfirst,hmid,htail]
  have hs1 := Finset.sum_range_id_mul_two (m-1)
  have hm1 : m-1+1=m := by omega
  have hm2 : m-1-1+2=m := by omega
  nlinarith



theorem odd_exception_inversions_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (oddException m)) :
    m*(m-1)+1 ≤ inversions (oddException (n := n) m) := by
  rw [← sum_depth_eq_inversions hd,← odd_depth_lower_sum m hm hn]
  exact Finset.sum_le_sum (fun i _ => odd_exception_depth_lower m hm hn hd i)



/-- The odd exceptional lift is at least one unit more expensive than the
conjectured diameter, so it cannot be a missing cheaper representation. -/
theorem odd_exception_price_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (oddException m))
    {g : List Letter} (hg : ScanTrace (oddException (n := n) m) g) :
    3*m^2-m+2 ≤ inversions (oddException (n := n) m)+paidRotations ((m+2 : ℕ) : Fin n) g := by
  have hI := odd_exception_inversions_lower m hm hn hd
  have hL := odd_exception_paid_rotation_lower m hm hn hd hg
  have hm1 : m-1+1=m := by omega
  have hn1 : n-1+1=n := by omega
  have he : m ≤ 3*m^2 := by nlinarith
  have hsub := Nat.sub_add_cancel he
  nlinarith







end LX.AffineScan

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
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem odd_exception_base (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) (i : Fin n) :
    oddBase m hm hn (((m+2 : ℕ)) : Fin n) i=oddException m i := by
  have hcv : (((m+2 : ℕ) : Fin n)).val=m+2 := Nat.mod_eq_of_lt (by omega)
  have hci := congrArg (fun k : ℕ => (k : ℤ)) hcv
  have hil := i.isLt
  unfold oddBase perturbedBoard
  change center (n := n) m (((((m+2 : ℕ)) : Fin n) : ℤ)+1-(oddRankValue m i.val : ℤ)-(i : ℤ))=oddException m i
  rw [hci]
  simp only [Nat.cast_add,Nat.cast_ofNat]
  by_cases hi0 : i.val=0
  · norm_num only [oddRankValue,oddException,hi0,Nat.cast_zero]
    simp only [ite_true,ite_false,false_and]
    apply center_eq_of_translate m _ _ 1 <;> (try constructor) <;> omega
  · by_cases hi1 : i.val=1
    · norm_num only [oddRankValue,oddException,hi1,Nat.cast_one]
      simp only [ite_true,ite_false,false_and]
      apply center_eq_of_translate m _ _ 1 <;> (try constructor) <;> omega
    · by_cases hi2 : i.val=2
      · norm_num only [oddRankValue,oddException,hi2,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
        simp only [ite_true,ite_false,false_and]
        apply center_eq_of_translate m _ _ 0 <;> (try constructor) <;> omega
      · have hi3 : 3 ≤ i.val := by omega
        by_cases hiM : i.val ≤ m+1
        · simp only [oddRankValue,oddException,ite_eq_right hi0,ite_eq_right hi1,
            ite_eq_right hi2,ite_eq_left hiM,ite_eq_left (show 3 ≤ i.val ∧ i.val ≤ m+1 from ⟨hi3,hiM⟩)]
          apply center_eq_of_translate m _ _ 0 <;> (try constructor) <;> omega
        · simp only [oddRankValue,oddException,ite_eq_right hi0,ite_eq_right hi1,
            ite_eq_right hi2,ite_eq_right hiM,
            ite_eq_right (show ¬(3 ≤ i.val ∧ i.val ≤ m+1) by omega)]
          apply center_eq_of_translate m _ _ (-1) <;> (try constructor) <;> omega

theorem odd_exception_balance (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    (∑ i : Fin n,oddException m i)=0 := by
  let f : ℕ → ℤ := fun k => if k=0 then 2-(m : ℤ) else if k=1 then -(m : ℤ)
    else if k=2 then 0 else if k ≤ m+1 then (m : ℤ)+4-2*k else 3*(m : ℤ)+4-2*k
  change (∑ i : Fin n,f i.val)=0
  rw [Fin.sum_univ_eq_sum_range,show n=3+(m-1)+(m-1) by omega,
    Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range 3,f k)=2-2*(m : ℤ) := by
    norm_num [Finset.sum_range_succ,f]
    ring
  have hmid : (∑ k ∈ Finset.range (m-1),f (3+k))=
      ((m-1 : ℕ) : ℤ)*((m : ℤ)-2)-2*∑ k ∈ Finset.range (m-1),(k : ℤ) := by
    have hp (k : ℕ) (hk : k ∈ Finset.range (m-1)) : f (3+k)=(m : ℤ)-2-2*k := by
      have := Finset.mem_range.mp hk
      dsimp only [f]
      split_ifs <;> push_cast <;> omega
    rw [Finset.sum_congr rfl hp]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring
  have htail : (∑ k ∈ Finset.range (m-1),f (3+(m-1)+k))=
      ((m-1 : ℕ) : ℤ)*(m : ℤ)-2*∑ k ∈ Finset.range (m-1),(k : ℤ) := by
    have hp (k : ℕ) (hk : k ∈ Finset.range (m-1)) : f (3+(m-1)+k)=(m : ℤ)-2*k := by
      dsimp only [f]
      split_ifs <;> push_cast <;> omega
    rw [Finset.sum_congr rfl hp]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hfirst,hmid,htail]
  have hs : (∑ j ∈ Finset.range (m-1),(j : ℤ))*2=((m-1 : ℕ) : ℤ)*((m-1-1 : ℕ) : ℤ) := by
    have hh := congrArg (fun t : ℕ => (t : ℤ)) (Finset.sum_range_id_mul_two (m-1))
    convert hh using 1 <;> simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] <;> rfl
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  have hm2 : ((m-1-1 : ℕ) : ℤ)=(m : ℤ)-2 := by omega
  rw [hm1,hm2] at hs
  rw [hm1]
  nlinarith




end LX.Antipode

end

namespace LX.Antipode
end LX.Antipode
open LX
open LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem solution (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {c : Fin n} (hc : c=((m+2 : ℕ) : Fin n)) {d : Fin n → ℤ}
    (hd : IsLift (odd m hm hn) (c : ℤ) d) {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-m+1 := by omega
  subst c
  have hbase : oddBase m hm hn (((m+2 : ℕ)) : Fin n)=oddException m :=
    funext (odd_exception_base m hm hn)
  rcases odd_unpaid_single_raise m hm hn hd hg hu with he | ⟨a,ha⟩
  · rw [hbase] at he
    rw [he] at hd hg hu
    have hh := odd_exception_price_lower m hm hn hd hg
    omega
  · have hz := hd.1
    rw [ha,hbase] at hz
    have hs : (∑ i : Fin n,raiseAt (oddException m) a i)=
        (∑ i : Fin n,oddException m i)+(n : ℤ) := by simp [raiseAt,Finset.sum_add_distrib]
    rw [hs,odd_exception_balance m hm hn] at hz
    have := NeZero.pos n
    omega
