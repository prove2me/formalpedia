-- Prove2me | solution 1 for LX.Core.FiniteCuts.unique_adjacent_matching_reflection
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:55:38.499808+00:00
-- url     : https://prove2.me/submissions/7983f558-9a7b-44c9-ac90-985c429ba852

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_NestedMatchingGeometry
import Theorems.Thm_LX_Core_FiniteCuts_nested_pair_endpoint_sum
import Theorems.Thm_LX_Core_FiniteCuts_noncrossing_pair_contains_adjacent

namespace LX.Core
end LX.Core
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts

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
namespace LX.Core.FiniteCuts
variable {n : ℕ}



/-- Two separated pair intervals would each contain a distinct adjacent pair. -/
theorem no_separated_pairs_of_unique_adjacent (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hfixed : ∀ i, p i ≠ i)
    (hunique : ∀ a b : Fin n, a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    NoSeparatedPairs p := by
  intro a b c d hab hbc hcd hpab hpcd
  obtain ⟨x,y,hx,hy,hxy,hpx⟩ := noncrossing_pair_contains_adjacent p hinv hnc a b hab hpab
    (fun i _ _ => hfixed i)
  obtain ⟨u,v,hu,hv,huv,hpu⟩ := noncrossing_pair_contains_adjacent p hinv hnc c d hcd hpcd
    (fun i _ _ => hfixed i)
  have heq := hunique x u (by rw [hpx]; exact hxy) (by rw [hpu]; exact huv)
  have := congrArg Fin.val heq
  omega





end LX.Core.FiniteCuts

end

namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
open LX
open LX.Core
open LX.Core.FiniteCuts
variable {n : ℕ}

/-- A fixed-point-free noncrossing matching with at most one adjacent pair is reversal. -/
theorem solution (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (hfixed : ∀ i, p i ≠ i)
    (hunique : ∀ a b : Fin n, a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i : Fin n, p i=i.rev := by
  have hsep := no_separated_pairs_of_unique_adjacent p hinv hnc hfixed hunique
  intro i
  have hne : (p i).val ≠ i.val := fun h => hfixed i (Fin.ext h)
  have hsum : i.val+(p i).val=n-1 := by
    by_cases hlt : i.val < (p i).val
    · exact nested_pair_endpoint_sum p hinv hnc hsep hfixed i (p i) hlt rfl
    · have h := nested_pair_endpoint_sum p hinv hnc hsep hfixed (p i) i (by omega) (hinv i)
      omega
  apply Fin.ext
  simp only [Fin.val_rev]
  omega
