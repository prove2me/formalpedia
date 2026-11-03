-- Prove2me | solution 1 for LX.Core.ZeroGap.maximal_event_support_pair
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:49:04.339036+00:00
-- url     : https://prove2.me/submissions/a8c762ac-3ea6-4263-8461-b4239e75fdb6

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
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_Core_ZeroGap_maximal_event_support_nodup

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
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

section
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]





theorem maximal_event_support_disjoint (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length) :
    (events.map eventSwap).Pairwise Equiv.Perm.Disjoint := by
  have hp := (List.nodup_flatMap.mp (maximal_event_support_nodup events hcard)).2
  apply List.pairwise_map.mpr
  apply hp.imp
  intro e f hef i
  change List.Disjoint [e.1,e.2] [f.1,f.2] at hef
  by_cases hi : i ∈ [e.1,e.2]
  · have hf : i ∉ [f.1,f.2] := List.disjoint_left.mp hef hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
    exact Or.inr (Equiv.swap_apply_of_ne_of_ne hf.1 hf.2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hi.1 hi.2)





end LX.Core.ZeroGap

end

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Every event is an actual pair of the product permutation in the maximal-support case. -/
theorem solution (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length)
    (e : Event n) (he : e ∈ events) :
    e.1 ≠ e.2 ∧ (events.map eventSwap).prod e.1=e.2 ∧
      (events.map eventSwap).prod e.2=e.1 := by
  have hn := (List.nodup_flatMap.mp (maximal_event_support_nodup events hcard)).1 e he
  have hne : e.1 ≠ e.2 := by simpa using hn
  have hd := maximal_event_support_disjoint events hcard
  have hm : eventSwap e ∈ events.map eventSwap := List.mem_map.mpr ⟨e,he,rfl⟩
  have hleft : e.1 ∈ (eventSwap e).support := by
    apply Equiv.Perm.mem_support.mpr
    simpa [eventSwap] using hne.symm
  have hright : e.2 ∈ (eventSwap e).support := by
    apply Equiv.Perm.mem_support.mpr
    simpa [eventSwap] using hne
  have hl := Equiv.Perm.eq_on_support_mem_disjoint hm hd e.1 hleft
  have hr := Equiv.Perm.eq_on_support_mem_disjoint hm hd e.2 hright
  exact ⟨hne, by simpa [eventSwap] using hl.symm, by simpa [eventSwap] using hr.symm⟩
