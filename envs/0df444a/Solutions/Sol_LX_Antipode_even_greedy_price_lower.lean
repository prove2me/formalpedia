-- Prove2me | solution 1 for LX.Antipode.even_greedy_price_lower
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:23:31.731544+00:00
-- url     : https://prove2.me/submissions/68d26cd9-556a-48e0-8de1-33fe37024344

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
import Definitions.Def_LX_EvenStrictBase
import Definitions.Def_LX_ExceptionalPrefixDelay
import Definitions.Def_LX_ExceptionalPriceLower
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
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
import Theorems.Thm_LX_AffineScan_even_exception_paid_rotation_lower
import Theorems.Thm_LX_AffineScan_exists_reflection_winding
import Theorems.Thm_LX_AffineScan_interval_depth_lower
import Theorems.Thm_LX_AffineScan_reflection_perturbation_pairs
import Theorems.Thm_LX_AffineScan_sum_depth_eq_inversions
import Theorems.Thm_LX_AffineScan_tail_head_depth_lower
import Theorems.Thm_LX_Antipode_even_boundary_base
import Theorems.Thm_LX_Antipode_even_exception_lift
import Theorems.Thm_LX_Antipode_even_ordinary_token_bound
import Theorems.Thm_LX_Antipode_even_strict_lift_unique
import Theorems.Thm_LX_Antipode_even_strict_minimum_location
import Theorems.Thm_LX_Antipode_even_strict_phase_parity
import Theorems.Thm_LX_Antipode_even_unpaid_strict_lower_strip
import Theorems.Thm_LX_Core_AffineLift_crossing_row_sum
import Theorems.Thm_LX_Core_FiniteCuts_adjacent_swap_inversion_price
import Theorems.Thm_LX_even_same_color_pairs_lower

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
/-! Integer residues and normalization of the phase of a balanced lift.
The normalized phase is represented by an element of `Fin n`. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast

variable {n : ℕ} [NeZero n]

theorem modulus_pos : (0 : ℤ) < n := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

theorem residue_val (z : ℤ) : ((Fin.intCast z : Fin n) : ℤ) = z % (n : ℤ) := by
  change ((z : Fin n).val : ℤ) = _
  rw [Fin.val_intCast]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt modulus_pos))

theorem modEq_residue (z : ℤ) :
    Int.ModEq (n : ℤ) z ((Fin.intCast z : Fin n) : ℤ) := by
  rw [residue_val]
  simp [Int.ModEq]

theorem normalize_phase {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) : IsLift p ((Fin.intCast c : Fin n) : ℤ) d := by
  refine ⟨hd.1, ?_⟩
  intro i
  exact (hd.2 i).trans ((modEq_residue c).add_left (p.symm i : ℤ))


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
namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift
variable {n : ℕ} [NeZero n]





theorem even_base_bounds (m : ℕ) (c i : Fin n) :
    -(m : ℤ) ≤ evenBase m c i ∧ evenBase m c i < (n : ℤ)-m := center_bounds m _







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



/-- The exceptional even lift cannot beat the conjectured diameter price.
The statement concerns this lift, not every lift of the antipode. -/
theorem even_exception_price_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LX.Core.AffineLift.IsLift p c (evenException m))
    {g : List Letter} (hg : ScanTrace (evenException (n := n) m) g) :
    3*m^2-4*m+3 ≤ inversions (evenException (n := n) m)+paidRotations ((m+3 : ℕ) : Fin n) g := by
  have hI := even_exception_inversions_lower m hm hn hd
  have hL := even_exception_paid_rotation_lower m hm hn hd hg
  have hm1 : m-1+1=m := by omega
  have hm2 : m-2+2=m := by omega
  have hn1 : n-1+1=n := by omega
  have he : 4*m ≤ 3*m^2 := by nlinarith
  have hsub := Nat.sub_add_cancel he
  nlinarith









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

/-- All lifts and all schedules of the even candidate meet the sharp
price. Height, phase and exceptional queue cases are discharged internally. -/
theorem solution (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-4*m+3 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-4*m+3 := by omega
  have hlo := even_unpaid_strict_lower_strip m hm hn hd hg hu
  rcases even_strict_phase_parity m hm hn hd hlo with hc | hpar
  · subst c
    have hsource := even_exception_lift m hm hn
    have hsource' := normalize_phase hsource
    change IsLift (even : State n) (((((m+3 : ℕ) : ℤ) : Fin n)) : ℤ) (evenException m) at hsource'
    have hsourceFin : IsLift (even : State n) ((((m+3 : ℕ) : Fin n)) : ℤ) (evenException m) := by
      simpa only [Int.cast_natCast] using hsource'
    have huniq := even_strict_lift_unique m (by omega) hn (((m+3 : ℕ)) : Fin n) hd hlo
    have huniqSource := even_strict_lift_unique m (by omega) hn (((m+3 : ℕ)) : Fin n) hsourceFin
      (fun i => (even_exception_strip m hm hn i).1)
    have hde : d=evenException m := huniq.trans huniqSource.symm
    rw [hde] at hg hu
    have hh := even_exception_price_lower m hm hn hsource hg
    omega
  · have hI := even_lift_inversions_lower m hm hn hd
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ) ≤ (inversions d : ℤ)+1 := by exact_mod_cast hI
    have hn' : (n : ℤ)=2*m := by omega
    have hm' : (3 : ℤ) ≤ m := by omega
    have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
    rw [hm1] at hI'
    have hrot : 2*(m : ℤ)^2-3*m+4 ≤ (paidRotations c g : ℤ) := by
      rcases even_strict_minimum_location m hm hn hd hlo hpar with hhead | ⟨j,hj,hmin⟩
      · have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
        have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
        have h01 : (0 : Fin n) ≠ 1 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv1] at this; omega
        have h02 : (0 : Fin n) ≠ 2 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv2] at this; omega
        have hq : -(even : State n).symm 0= -(1 : Fin n) := by
          change -(1-Equiv.swap (1 : Fin n) 2 0)= -1
          rw [Equiv.swap_apply_of_ne_of_ne h01 h02,sub_zero]
        have hqval : ((-(1 : Fin n)).val : ℤ)=(n : ℤ)-1 := by
          rw [Fin.val_neg,ite_eq_right (Ne.symm h01),hv1]
          omega
        have ht := hg.paid_token_bound (by omega : 2 ≤ n) hd 0
        rw [hq,hqval] at ht
        simp only [targets,hhead,Fin.val_zero,Nat.cast_zero,Nat.zero_sub,mul_zero,zero_add,zero_sub] at ht
        nlinarith
      · have ht := even_ordinary_token_bound (by omega : 3 ≤ n) hd hg j (by omega)
        rw [hmin] at ht
        have hj' : (m : ℤ)+2 ≤ j := by omega
        nlinarith
    have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-4*m+3 : ℕ) : ℤ) := by
      exact_mod_cast hu
    rw [Nat.cast_add,Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)] at hu'
    push_cast at hu'
    nlinarith
