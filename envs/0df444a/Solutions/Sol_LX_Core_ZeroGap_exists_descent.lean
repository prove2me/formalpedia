-- Prove2me | solution 1 for LX.Core.ZeroGap.exists_descent
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:43:24.481171+00:00
-- url     : https://prove2.me/submissions/e59a6042-9213-415b-bb65-682f077c2390

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
import Definitions.Def_LX_RecenteredLift
import Definitions.Def_LX_ZeroGapExchange
import Definitions.Def_LX_ZeroGapInversionTerms
import Definitions.Def_LX_ZeroGapPair
import Theorems.Thm_LX_Core_RotationWords_inversion_count_recentered
import Theorems.Thm_LX_Core_RotationWords_recentered_lift
import Theorems.Thm_LX_Core_ZeroGap_endpoint_swap_inversions
import Theorems.Thm_LX_Core_ZeroGap_exchange_lift
import Theorems.Thm_LX_Core_ZeroGap_exchange_short
import Theorems.Thm_LX_Core_ZeroGap_exchange_sum
import Theorems.Thm_LX_Core_ZeroGap_exists_zero_gap
import Theorems.Thm_LX_Core_ZeroGap_negative_endpoint_length
import Theorems.Thm_LX_Core_ZeroGap_positive_endpoint_length

namespace Int
end Int
namespace LX
end LX
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
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
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
/-! A zero-displacement phase lift is an actual rotation. Its final rotation
is explicitly paid by an LX.Core word of length at most n-1. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem rotation_power_apply (k : ℕ) (i : Fin n) : (L n ^ k) i = i + (k : Fin n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [L, finRotate_apply, Nat.cast_add, add_comm, add_left_comm]


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
/-! Recenter a phase lift at an arbitrary port. The local target is chosen so
that paid entry and exit rotations recover the original visible permutation. -/
namespace LX.Core.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem local_displacement_zero (d : Fin n → ℤ) (r : Fin n) :
    localDisplacement d r 0=d r := by
  simp [localDisplacement, AffineLift.rotation_power_apply]



omit [NeZero n] in
theorem local_displacement_mass (d : Fin n → ℤ) (r : Fin n) :
    (∑ i : Fin n, |localDisplacement d r i|)=∑ i : Fin n, |d i| := by
  exact Equiv.sum_comp (L n^r.val) (fun i => |d i|)


end LX.Core.RotationWords

end

section
/-! Recenter the zero-gap pair and derive the required endpoint inequalities
from injectivity of the actual target permutation. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem centered_pair (d : Fin n → ℤ) (hd : ∑ i, d i=0) (hne : ∃ i, d i ≠ 0) :
    ∃ u v : Fin n, 0 < RotationWords.localDisplacement d u 0 ∧
      RotationWords.localDisplacement d u v < 0 ∧ 0 < v.val ∧
      ∀ j, 0 < j.val → j.val < v.val → RotationWords.localDisplacement d u j=0 := by
  obtain ⟨u,w,hu,hw,hdist,hgap⟩ := exists_zero_gap d hd hne
  refine ⟨u,w-u,?_,?_,hdist,?_⟩
  · simpa only [RotationWords.local_displacement_zero] using hu
  · simpa [RotationWords.localDisplacement,AffineLift.rotation_power_apply] using hw
  · intro j hj hj'
    have he : distance u (j+u)=j.val := by simp [distance]
    have hz := hgap (j+u) (by omega) (by rw [he]; exact hj')
    simpa only [RotationWords.localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self] using hz










end LX.Core.ZeroGap

end

section
/-! Swapping the endpoints of a zero gap gives a balanced shorter lift.
The exact drop in displacement mass is twice the gap length. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]







theorem exchange_mass (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0)
    (hpos : (v : ℤ) ≤ d 0) (hneg : (v : ℤ) ≤ -d v) :
    (∑ i : Fin n, |exchange d v i|)=(∑ i : Fin n, |d i|)-2*(v : ℤ) := by
  have h := exchange_sum d v hv (fun z => |z|)
  have hv0 : (0 : ℤ) ≤ v := by positivity
  rw [abs_of_nonpos (by omega : (v : ℤ)+d v ≤ 0),abs_of_nonneg (by omega : 0 ≤ d 0),
    abs_of_nonneg (by omega : 0 ≤ d 0-(v : ℤ)),abs_of_nonpos (by omega : d v ≤ 0)] at h
  omega








end LX.Core.ZeroGap

end

section
/-! Every nonzero short balanced lift has a genuine endpoint-transposition
step with exact displacement and affine-inversion decreases. -/
namespace LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem exchange_endpoints (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0) :
    (fun i : Fin n => (i : ℤ)+exchange d v i)=swapEndpoints (fun i : Fin n => (i : ℤ)+d i) v := by
  funext i
  by_cases hi : i=0
  · subst i
    simp [exchange,swapEndpoints]
  · by_cases hiv : i=v
    · subst i
      simp [exchange,swapEndpoints,hv]
    · simp [exchange,swapEndpoints,hi,hiv,Equiv.swap_apply_of_ne_of_ne hi hiv]

theorem exchange_inversions {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (v : Fin n) (hv : 0 < v.val) (hpos : 0 < d 0) (hneg : d v < 0)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → d i=0) :
    LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)=
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+exchange d v i)+(2*v.val-1) := by
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  have hA := positive_endpoint_length hd v hpos hgap
  have hB := negative_endpoint_length hd v hneg hgap
  have hs0 := hshort 0
  have hsv := hshort v
  rw [abs_of_pos hpos] at hs0
  rw [abs_of_neg hneg] at hsv
  rw [exchange_endpoints d v hv0]
  apply endpoint_swap_inversions (fun i : Fin n => (i : ℤ)+d i) v hv
  · simpa using hA
  · omega
  · simp only [Fin.val_zero,Int.natCast_zero,zero_add]
    omega
  · intro i hi hi'
    simp only [hgap i hi hi',add_zero]





end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) (hne : ∃ i, d i ≠ 0) :
    ∃ u v : Fin n,
      0 < v.val ∧ 0 < RotationWords.localDisplacement d u 0 ∧ RotationWords.localDisplacement d u v < 0 ∧
      (∀ i : Fin n, 0 < i.val → i.val < v.val → RotationWords.localDisplacement d u i=0) ∧
      AffineLift.IsLift (Equiv.swap 0 v*RotationWords.localTarget p 0 u) 0
        (exchange (RotationWords.localDisplacement d u) v) ∧
      (∀ i, 2*|exchange (RotationWords.localDisplacement d u) v i| < (n : ℤ)) ∧
      (∑ i : Fin n, |d i|)=(∑ i : Fin n, |exchange (RotationWords.localDisplacement d u) v i|)+2*(v : ℤ) ∧
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)=
        LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+exchange (RotationWords.localDisplacement d u) v i)+
          (2*v.val-1) := by
  obtain ⟨u,v,hpos,hneg,hv,hgap⟩ := centered_pair d hd.1 hne
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  have hlocal := RotationWords.recentered_lift (0 : Fin n) u (by simpa using hd)
  have hs : ∀ i, 2*|RotationWords.localDisplacement d u i| < (n : ℤ) := by
    intro i
    exact hshort ((L n^u.val) i)
  have hA := positive_endpoint_length hlocal v hpos hgap
  have hB := negative_endpoint_length hlocal v hneg hgap
  refine ⟨u,v,hv,hpos,hneg,hgap,exchange_lift hlocal v hv0,exchange_short _ v hv0 hA hB hs,?_,?_⟩
  · have hm := exchange_mass (RotationWords.localDisplacement d u) v hv0 hA hB
    rw [RotationWords.local_displacement_mass] at hm
    omega
  · have h := exchange_inversions hlocal hs v hv hpos hneg hgap
    rw [RotationWords.inversion_count_recentered (0 : Fin n) u (by simpa using hd)] at h
    exact h
