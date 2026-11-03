-- Prove2me | solution 1 for LX.Core.ZeroGap.graph_edges_le_events
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:35:21.641296+00:00
-- url     : https://prove2.me/submissions/e8fc73c2-a06e-4323-bd77-5379950b0490

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
import Definitions.Def_LX_ZeroGapEventGeometry
import Definitions.Def_LX_ZeroGapEventGraph

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (events : List (Event n)) (f : α → Fin n) (hf : Function.Injective f)
    (hedge : ∀ i j, G.Adj i j → EventEdge events (f i) (f j)) :
    Nat.card G.edgeSet ≤ events.length := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hmem : ∀ q, q ∈ G.edgeFinset → Sym2.map f q ∈ events.toFinset.image (fun e => Sym2.mk e.1 e.2) := by
    intro q
    refine Sym2.inductionOn q ?_
    intro i j hq
    have ha : G.Adj i j := (G.mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp hq)
    obtain ⟨e,he,h⟩ := hedge i j ha
    apply Finset.mem_image.mpr
    refine ⟨e,List.mem_toFinset.mpr he,?_⟩
    rcases h with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · simpa only [Sym2.map_mk,hi,hj]
    · simpa only [Sym2.map_mk,hi,hj] using (Sym2.eq_swap (a := e.1) (b := e.2))
  have hsub : G.edgeFinset.image (Sym2.map f) ⊆ events.toFinset.image (fun e => Sym2.mk e.1 e.2) := by
    intro q hq
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hq
    exact hmem e he
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (Sym2.map.injective hf)] at hc
  have hl : (events.toFinset.image (fun e => Sym2.mk e.1 e.2)).card ≤ events.length :=
    Finset.card_image_le.trans (List.toFinset_card_le events)
  rw [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card]
  exact hc.trans hl
