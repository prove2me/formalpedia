-- Prove2me | solution 1 for LX.Antipode.even_boundary_inversions_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:11:12.534689+00:00
-- url     : https://prove2.me/submissions/78761495-2326-4338-b658-39d483f4a182

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
import Definitions.Def_LX_BackwardDepth
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_EvenSingleRaise
import Definitions.Def_LX_ExceptionalPrefixDelay
import Definitions.Def_LX_ExceptionalPriceLower
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhaseMinimumRescue
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_WordReflection
import Theorems.Thm_LX_AffineScan_exists_depth_extreme
import Theorems.Thm_LX_AffineScan_interval_depth_lower
import Theorems.Thm_LX_AffineScan_raise_coordinate_inversions
import Theorems.Thm_LX_AffineScan_sum_depth_eq_inversions
import Theorems.Thm_LX_AffineScan_tail_head_depth_lower
import Theorems.Thm_LX_Antipode_even_boundary_base
import Theorems.Thm_LX_Antipode_even_exception_balance
import Theorems.Thm_LX_Antipode_even_exception_lift
import Theorems.Thm_LX_CenteredLift_balanced_single_raise
import Theorems.Thm_LX_CenteredLift_even_perturbed_board_mass
import Theorems.Thm_LX_Core_AffineLift_crossing_row_sum

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

section
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]



theorem even_base_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (c : Fin n) :
    -(n : ℤ) ≤ ∑ i,evenBase m c i := even_perturbed_board_mass m hm hn ((c : ℤ)+1)

theorem even_base_bounds (m : ℕ) (c i : Fin n) :
    -(m : ℤ) ≤ evenBase m c i ∧ evenBase m c i < (n : ℤ)-m := center_bounds m _

theorem even_base_residue (m : ℕ) (c : Fin n)
    {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even (c : ℤ) d) (i : Fin n) :
    (d i : Fin n)=(evenBase m c i : Fin n) := by
  have hh := LX.Core.AffineLift.lift_residue hd i
  simp only [even,Equiv.symm_symm,Equiv.Perm.mul_apply,LX.Core.WordReflection.reflection_apply,
    Int.cast_natCast,Fin.cast_val_eq_self] at hh
  change (d i : Fin n)=(center (n := n) m (((c : ℤ)+1)-((Equiv.swap (1 : Fin n) 2) i : ℤ)-(i : ℤ)) : Fin n)
  rw [center_cast]
  simp only [Int.cast_sub,Int.cast_add,Int.cast_one,Int.cast_natCast,Fin.cast_val_eq_self]
  linear_combination hh

theorem even_lift_single_raise (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (c : Fin n)
    {d : Fin n → ℤ} (hd : LX.Core.AffineLift.IsLift even (c : ℤ) d)
    (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    d=evenBase m c ∨ ∃ a,d=raiseAt (evenBase m c) a := by
  exact balanced_single_raise m d (evenBase m c) hd.1 hlo
    (even_base_bounds m c) (even_base_residue m c hd) (even_base_mass m hm hn c)



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



end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]





theorem even_boundary_base_mass (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    (∑ i : Fin n,evenBase m (((m+2 : ℕ)) : Fin n) i)= -(n : ℤ) := by
  simp only [even_boundary_base m hm hn,Finset.sum_sub_distrib,even_exception_balance m hm hn]
  simp



end LX.Antipode

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]









theorem even_exception_depth_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (evenException m))
    (i : Fin n) : evenDepthLower m i.val ≤ backwardDepth (evenException m) i := by
  have hil := i.isLt
  unfold evenDepthLower
  split_ifs with hi0 hi2 hiM
  · have hi : i=0 := Fin.ext hi0
    subst i
    have hh := tail_head_depth_lower (evenException (n := n) m) (⟨m+2,by omega⟩ : Fin n) (by
      intro j hj
      have hjl := j.isLt
      have hjp : m+2 ≤ j.val := hj
      simp only [targets,evenException,Fin.val_zero,Nat.cast_zero,ite_true,zero_add]
      rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : ¬j.val ≤ 2),
        ite_eq_right (by omega : ¬j.val ≤ m+1)]
      omega)
    simpa only [show n-(m+2)=m-2 by omega] using hh
  · have hh := neg_displacement_le_depth hd i
    simp only [evenException,ite_eq_right hi0,ite_eq_left hi2] at hh
    omega
  · apply interval_depth_lower (evenException m) (⟨3,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : 3 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,evenException,ite_eq_right hi0,ite_eq_right hi2,ite_eq_left hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : ¬j.val ≤ 2),
      ite_eq_left (by omega : j.val ≤ m+1)]
    omega
  · apply interval_depth_lower (evenException m) (⟨m+2,by omega⟩ : Fin n) i
    intro j hj hji
    have hjp : m+2 ≤ j.val := hj
    have hjl : j.val < i.val := hji
    simp only [targets,evenException,ite_eq_right hi0,ite_eq_right hi2,ite_eq_right hiM]
    rw [ite_eq_right (by omega : j.val ≠ 0),ite_eq_right (by omega : ¬j.val ≤ 2),
      ite_eq_right (by omega : ¬j.val ≤ m+1)]
    omega



omit [NeZero n] in
theorem even_depth_lower_sum (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    ∑ i : Fin n,evenDepthLower m i.val=m*(m-1) := by
  rw [Fin.sum_univ_eq_sum_range,show n=3+(m-1)+(m-2) by omega,
    Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range 3,evenDepthLower m k)=(m-2)+2*(m-1) := by
    norm_num [Finset.sum_range_succ,evenDepthLower]
    omega
  have hmid : (∑ k ∈ Finset.range (m-1),evenDepthLower m (3+k))=
      ∑ k ∈ Finset.range (m-1),k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    unfold evenDepthLower
    split_ifs <;> omega
  have htail : (∑ k ∈ Finset.range (m-2),evenDepthLower m (3+(m-1)+k))=
      ∑ k ∈ Finset.range (m-2),k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold evenDepthLower
    split_ifs <;> omega
  rw [hfirst,hmid,htail]
  have hs1 := Finset.sum_range_id_mul_two (m-1)
  have hs2 := Finset.sum_range_id_mul_two (m-2)
  have hm1 : m-1+1=m := by omega
  have hm2 : m-2+2=m := by omega
  have hm3 : m-2-1+3=m := by omega
  have he : m-1-1=m-2 := by omega
  rw [he] at hs1
  nlinarith



theorem even_exception_inversions_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (evenException m)) :
    m*(m-1) ≤ inversions (evenException (n := n) m) := by
  rw [← sum_depth_eq_inversions hd,← even_depth_lower_sum m hm hn]
  exact Finset.sum_le_sum (fun i _ => even_exception_depth_lower m hm hn hd i)













end LX.AffineScan

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
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem even_exception_strip (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) (i : Fin n) :
    1-(m : ℤ) ≤ evenException m i ∧ evenException m i ≤ (m : ℤ) := by
  have hh := even_base_bounds m (((m+2 : ℕ)) : Fin n) i
  rw [even_boundary_base m hm hn] at hh
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

/-- Every lower-strip lift in phase m+2 has two more inversions than the
coarse uniform lower estimate. This closes the boundary-height branch. -/
theorem solution (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hc : c=((m+2 : ℕ) : Fin n)) (hlo : ∀ i,-(m : ℤ) ≤ d i) :
    m*(m-1)+1 ≤ inversions d := by
  subst c
  rcases even_lift_single_raise m (by omega) hn (((m+2 : ℕ)) : Fin n) hd hlo with hbase | ⟨a,ha⟩
  · have hz := hd.1
    rw [hbase,even_boundary_base_mass m hm hn] at hz
    have := NeZero.pos n
    omega
  · have hsource := even_exception_lift m hm hn
    have hw : ∀ i j : Fin n,evenException m i-evenException m j < (n : ℤ) := by
      intro i j
      have hi := even_exception_strip m hm hn i
      have hj := even_exception_strip m hm hn j
      omega
    have hlow : ∀ i,-(((m-1 : ℕ) : ℤ)) ≤ evenException (n := n) m i := by
      intro i
      have hh := even_exception_strip m hm hn i
      omega
    have he : d=raiseMinimum (evenException m) a := by
      rw [ha]
      funext i
      rw [raise_minimum_apply]
      simp only [raiseAt,even_boundary_base m hm hn,Nat.cast_ite,Nat.cast_zero]
    have hprice := raise_coordinate_inversions_lower hsource a hw (m-1) hlow
    rw [← he] at hprice
    have hI := even_exception_inversions_lower m hm hn hsource
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ) ≤ (inversions (evenException (n := n) m) : ℤ) := by
      exact_mod_cast hI
    have hgoal : (m : ℤ)*((m-1 : ℕ) : ℤ)+1 ≤ (inversions d : ℤ) := by
      have hn' : (n : ℤ)=2*m := by omega
      have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
      nlinarith
    exact_mod_cast hgoal
