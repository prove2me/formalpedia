-- Prove2me | solution 1 for LX.AffineScan.top_phase_inversions
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:34:36.511627+00:00
-- url     : https://prove2.me/submissions/2ecc1184-efe3-4b9c-b130-70fe2836053e

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_InversionSet
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ScanInversions
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_AffineLift_crossing_antisymm
import Theorems.Thm_LX_Core_AffineLift_crossing_row_sum
import Theorems.Thm_LX_Core_RotationWords_twice_inversion_count

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
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators













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
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Changing a phase alters each signed crossing by the difference of the
selected endpoint indicators. -/
theorem phase_shift_crossing (d : Fin n → ℤ) (S : Finset (Fin n)) (i j : Fin n) :
    crossing (phaseShift d S) i j=crossing d i j-
      (if i ∈ S then (1 : ℤ) else 0)+(if j ∈ S then (1 : ℤ) else 0) := by
  have he : crossingNumerator (phaseShift d S) i j=crossingNumerator d i j+
      ((if i ∈ S then (1 : ℤ) else 0)-(if j ∈ S then (1 : ℤ) else 0))*(n : ℤ) := by
    unfold crossingNumerator phaseShift
    split_ifs <;> ring
  rw [crossing,he,Int.add_mul_ediv_right _ _ (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)]
  unfold crossing
  ring

theorem ordered_crossing_bounds (d : Fin n → ℤ) (i j : Fin n)
    (horder : d j ≤ d i) (hwidth : d i-d j < (n : ℤ)) :
    0 ≤ crossing d i j ∧ crossing d i j ≤ 1 := by
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hv := (j-i).isLt
  have hlo : -(n : ℤ) ≤ crossingNumerator d i j := by
    unfold crossingNumerator
    omega
  have hhi : crossingNumerator d i j < (n : ℤ) := by
    unfold crossingNumerator
    omega
  have hqlo := (Int.le_ediv_iff_mul_le hn).mpr (show (-1 : ℤ)*n ≤ crossingNumerator d i j by omega)
  have hqhi := (Int.ediv_lt_iff_lt_mul hn).mpr (show crossingNumerator d i j < (1 : ℤ)*n by omega)
  unfold crossing
  omega







end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Exact exchange-price change when a top set of a strict-width lift is
wrapped through the phase seam. Ties may be selected individually. -/
theorem solution {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (S : Finset (Fin n))
    (hwidth : ∀ i j, d i-d j < (n : ℤ))
    (htop : ∀ i ∈ S, ∀ j ∉ S, d j ≤ d i) :
    (inversions (phaseShift d S) : ℤ)-inversions d=
      (S.card : ℤ)*((n : ℤ)-S.card)-2*∑ i ∈ S,d i := by
  let χ := fun i : Fin n => if i ∈ S then (1 : ℤ) else 0
  have hχ : (∑ i : Fin n,χ i)=(S.card : ℤ) := by simp [χ]
  have hpoint (i j : Fin n) :
      |crossing (phaseShift d S) i j|-|crossing d i j|=
        χ i+χ j-2*(χ i*χ j)-2*(χ i*crossing d i j)+2*(χ j*crossing d i j) := by
    rw [phase_shift_crossing]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · simp [χ,hi,hj]
    · have hb := ordered_crossing_bounds d i j (htop i hi j hj) (hwidth i j)
      have hc : crossing d i j=0 ∨ crossing d i j=1 := by omega
      rcases hc with hc | hc <;> simp [χ,hi,hj,hc]
    · have hb := ordered_crossing_bounds d j i (htop j hj i hi) (hwidth j i)
      have hanti := crossing_antisymm hd i j
      have hc : crossing d i j=0 ∨ crossing d i j= -1 := by omega
      rcases hc with hc | hc <;> simp [χ,hi,hj,hc]
    · simp [χ,hi,hj]
  have h1 : (∑ i : Fin n, ∑ _j : Fin n, χ i)=(n : ℤ)*S.card := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Finset.mul_sum,hχ]
  have h2 : (∑ _i : Fin n, ∑ j : Fin n, χ j)=(n : ℤ)*S.card := by simp [hχ]
  have h3 : (∑ i : Fin n, ∑ j : Fin n, χ i*χ j)=(S.card : ℤ)^2 := by
    simp_rw [← Finset.mul_sum,hχ]
    rw [← Finset.sum_mul,hχ]
    ring
  have h4 : (∑ i : Fin n, ∑ j : Fin n, χ i*crossing d i j)=∑ i ∈ S,d i := by
    simp_rw [← Finset.mul_sum,crossing_row_sum hd]
    simp [χ,Finset.sum_filter]
  have h5 : (∑ i : Fin n, ∑ j : Fin n, χ j*crossing d i j)= -(∑ i ∈ S,d i) := by
    rw [Finset.sum_comm]
    have he : (∑ j : Fin n, ∑ i : Fin n, χ j*crossing d i j)=
        ∑ j : Fin n, ∑ i : Fin n, -(χ j*crossing d j i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [crossing_antisymm hd i j]
      ring
    rw [he]
    simp only [Finset.sum_neg_distrib]
    exact congrArg Neg.neg h4
  have htwo (f : Fin n → Fin n → ℤ) : (∑ i : Fin n, ∑ j : Fin n, 2*f i j)=
      2*(∑ i : Fin n, ∑ j : Fin n, f i j) := by simp_rw [← Finset.mul_sum]
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
      (|crossing (phaseShift d S) i j|-|crossing d i j|))=
      2*((S.card : ℤ)*((n : ℤ)-S.card)-2*∑ i ∈ S,d i) := by
    simp only [hpoint,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [htwo,htwo,htwo,h1,h2,h3,h4,h5]
    ring
  have hold := LX.Core.RotationWords.twice_inversion_count hd
  have hnew := LX.Core.RotationWords.twice_inversion_count (shift_lift hd S)
  have hold' : 2*(inversions d : ℤ)=∑ i : Fin n, ∑ j : Fin n, |crossing d i j| := by
    change 2*(LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=_
    have hc := congrArg (fun k : ℕ => (k : ℤ)) hold
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hc
  have hnew' : 2*(inversions (phaseShift d S) : ℤ)=
      ∑ i : Fin n, ∑ j : Fin n, |crossing (phaseShift d S) i j| := by
    change 2*(LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+phaseShift d S i) : ℤ)=_
    have hc := congrArg (fun k : ℕ => (k : ℤ)) hnew
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hc
  simp only [Finset.sum_sub_distrib] at hsum
  rw [← hold',← hnew'] at hsum
  omega
