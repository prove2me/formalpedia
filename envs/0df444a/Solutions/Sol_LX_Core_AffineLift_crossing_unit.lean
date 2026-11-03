-- Prove2me | solution 1 for LX.Core.AffineLift.crossing_unit
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:32:15.28922+00:00
-- url     : https://prove2.me/submissions/dfe00088-6b07-482a-84b5-b632b18bd11a

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
import Theorems.Thm_LX_Core_AffineLift_short_coordinates

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
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
/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators


























theorem range_bound {n : ℕ} {d : Fin n → ℤ}
    (hd : ∑ i, d i = 0) (hm : Majorized d) (i j : Fin n) :
    d i - d j ≤ (n : ℤ) - 1 := by
  obtain ⟨hi, _⟩ := short_coordinates hd hm i
  obtain ⟨_, hj⟩ := short_coordinates hd hm j
  omega

end LX.Core.AffineLift

end

section
/-! Integer residues and normalization of the phase of a balanced lift.
The normalized phase is represented by an element of `Fin n`. -/
namespace LX.Core.AffineLift
open scoped Fin.IntCast Fin.NatCast

variable {n : ℕ} [NeZero n]

theorem modulus_pos : (0 : ℤ) < n := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)








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

namespace LX.Core.AffineLift
end LX.Core.AffineLift
open LX
open LX.Core
open LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- In a majorized lift, each signed pair crossing is -1, 0 or 1. -/
theorem solution {d : Fin n → ℤ} (hd : ∑ i, d i = 0)
    (hm : Majorized d) (i j : Fin n) : |crossing d i j| ≤ 1 := by
  have hab := range_bound hd hm i j
  have hba := range_bound hd hm j i
  have hlo : (0 : ℤ) ≤ ((j-i : Fin n) : ℤ) := by omega
  have hhi : ((j-i : Fin n) : ℤ) < n := by exact_mod_cast (j-i).isLt
  have hnumlo : -(n : ℤ) ≤ crossingNumerator d i j := by
    dsimp [crossingNumerator]; omega
  have hnumhi : crossingNumerator d i j < 2 * (n : ℤ) := by
    dsimp [crossingNumerator]; omega
  have hqlo : -1 ≤ crossingNumerator d i j / (n : ℤ) :=
    (Int.le_ediv_iff_mul_le (modulus_pos (n := n))).mpr (by simpa using hnumlo)
  have hqhi : crossingNumerator d i j / (n : ℤ) < 2 :=
    (Int.ediv_lt_iff_lt_mul (modulus_pos (n := n))).mpr hnumhi
  rw [abs_le]
  dsimp [crossing]
  omega
