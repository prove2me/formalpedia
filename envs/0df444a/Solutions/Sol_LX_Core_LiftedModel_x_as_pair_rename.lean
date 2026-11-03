-- Prove2me | solution 1 for LX.Core.LiftedModel.x_as_pair_rename
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:30:59.203073+00:00
-- url     : https://prove2.me/submissions/d5aef8a1-03b1-4118-a931-4c3222a196f3

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_LiftedPair
import Definitions.Def_LX_LiftedRename
import Definitions.Def_LX_PhysicalModel

namespace Int
end Int
namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
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
/-! A lifted pair is a pair of finite labels together with an integer relative
copy offset. Equal pair events implement the same periodic involution. -/
namespace LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]








omit [NeZero n] in
theorem configuration_ext_components {s t : Configuration n}
    (hp : s.physical=t.physical) (hz : s.position=t.position) (hc : s.cursor=t.cursor) : s=t := by
  cases s
  cases t
  cases hp
  cases hz
  cases hc
  rfl









end LX.Core.LiftedModel

end

namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
open LX
open LX.Core
open LX.Core.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem solution (s : Configuration n) (a b : Fin n) (hab : a ≠ b)
    (ha : s.physical.tokens s.physical.cursor=a)
    (hb : s.physical.tokens (s.physical.cursor+1)=b) :
    step .x s=pairRename a b (s.position a+1-s.position b) s := by
  apply configuration_ext_components
  · have ht : s.physical.tokens*Equiv.swap s.physical.cursor (s.physical.cursor+1)=
        (Equiv.swap a b).symm*s.physical.tokens := by
      apply Equiv.ext
      intro i
      simpa only [Equiv.Perm.mul_apply, Equiv.symm_swap, ha, hb] using
        Function.Injective.map_swap s.physical.tokens.injective s.physical.cursor
          (s.physical.cursor+1) i
    simpa only [step, PhysicalModel.step, pairRename, rename] using
      congrArg (fun q => PhysicalModel.Configuration.mk q s.physical.cursor) ht
  · funext i
    simp only [step, pairRename, rename, ha, hb]
    by_cases hi : i=a
    · subst i
      simp [pairOffset, hab]
    · by_cases hj : i=b
      · subst i
        simp [pairOffset, Ne.symm hab]
        ring
      · simp [pairOffset, hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]
  · simp [step, increment, pairRename, rename]
