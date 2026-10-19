-- Prove2me | solution 1 for OAI.Barnette.Network.Triangle.index_delta
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:58:27.188529+00:00
-- url     : https://prove2.me/submissions/32b7878e-f277-46d2-a1ee-ad9c571ae299

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean:L294-L318
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Triangle.index_delta. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem

-- ---- from OAI.Combinatorics.Hamiltonian.Circulation ----
namespace OAI

/-! Oriented triangular faces and positive white-face charges. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma arcSign_opposite {e : E} {v w : F}
    (hne : v ≠ w) (he : s(D.tail e,D.head e) = s(v,w)) :
    D.arcSign e w = - D.arcSign e v := by
  rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩
  · simp [arcSign,ht,hne]
  · simp [arcSign,ht,hne.symm]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.TriangleSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

namespace State

variable {T} {X : Set V}

end State

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackGradient_face (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) {v : V}
    (hv : black v) {e : E} (he : N.Incident e v) :
    N.gradient (fun w => if black w then 1 else 0) e =
      N.gradient (fun w => if w = v then 1 else 0) e := by
  have hcol := hc e
  rcases he with ht | hh
  · have hhead : ¬black (N.head e) := (hc e).mp (ht ▸ hv)
    have hne : N.head e ≠ v := fun hh => hhead (hh ▸ hv)
    simp [gradient_apply,ht,hhead,hne,hv]
  · have htail : ¬black (N.tail e) := fun ht => (hc e).mp ht (hh ▸ hv)
    have hne : N.tail e ≠ v := fun ht => htail (ht ▸ hv)
    simp [gradient_apply,hh,htail,hne,hv]

omit [Fintype V] [Fintype F] in
lemma Triangle.index_delta (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (hv : black v)
    {i j : Fin 3} (hij : i ≠ j) :
    (Barnette.TriangleSystem.indexDelta i j : ℝ) =
      N.gradient (fun w => if black w then 1 else 0) (t.side D i j) *
        D.arcSign (t.side D i j) (t.corner i) := by
  rw [N.blackGradient_face black hc hv ((N.mem_star _ _).mp (t.side_mem D i j))]
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [TriangleSystem.indexDelta,ite_eq_right hij,Int.cast_one,side,ite_eq_left hj,ht]
    unfold arcSign
    split_ifs <;> norm_num
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [TriangleSystem.indexDelta,ite_eq_right hij,ite_eq_right hj,Int.cast_neg,Int.cast_one,side,ht]
    have hne : t.corner j ≠ t.corner i := fun h => hij (t.corner_injective h).symm
    have he : s(D.tail (t.edge j),D.head (t.edge j)) = s(t.corner j,t.corner i) := by
      rw [t.edge_ends,hi]
    rw [D.arcSign_opposite hne he]
    unfold arcSign
    split_ifs <;> norm_num

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.Triangle.index_delta := @_root_.OAI.Barnette.Network.Triangle.index_delta
