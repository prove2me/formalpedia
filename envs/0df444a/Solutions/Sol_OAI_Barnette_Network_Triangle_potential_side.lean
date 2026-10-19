-- Prove2me | solution 1 for OAI.Barnette.Network.Triangle.potential_side
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:56:31.884786+00:00
-- url     : https://prove2.me/submissions/1ee7bb13-5757-48f3-a2b8-4dbfc3090d29

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean:L256-L277
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Triangle.potential_side. The node keeps its source
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
lemma Triangle.potential_step {s : Finset E} (t : D.Triangle s) (α : E → ℝ)
    (hα : ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = 0) (i : Fin 3) :
    t.potential D α (i+1) - t.potential D α i =
      α (t.edge i) * D.arcSign (t.edge i) (t.corner i) := by
  have hs : α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0) +
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1) +
      α (t.edge 2) * D.arcSign (t.edge 2) (t.corner 2) = 0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hα
  fin_cases i
  · change t.potential D α 1 - t.potential D α 0 =
      α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0)
    simp [potential]
  · change t.potential D α 2 - t.potential D α 1 =
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1)
    simp [potential]
  · change t.potential D α 0 - t.potential D α 2 =
      α (t.edge 2) * D.arcSign (t.edge 2) (t.corner 2)
    simp [potential]
    linarith

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.potential_side {s : Finset E} (t : D.Triangle s) (α : E → ℝ)
    (hα : ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = 0)
    {i j : Fin 3} (hij : i ≠ j) :
    t.potential D α j - t.potential D α i =
      α (t.side D i j) * D.arcSign (t.side D i j) (t.corner i) := by
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [side,ite_eq_left hj]
    rw [hj]
    exact t.potential_step D α hα i
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [side,ite_eq_right hj]
    have hne : t.corner j ≠ t.corner i := fun h => hij (t.corner_injective h).symm
    have he : s(D.tail (t.edge j),D.head (t.edge j)) = s(t.corner j,t.corner i) := by
      rw [t.edge_ends,hi]
    rw [D.arcSign_opposite hne he]
    have hs := t.potential_step D α hα j
    rw [← hi] at hs
    linarith

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.Triangle.potential_side := @_root_.OAI.Barnette.Network.Triangle.potential_side
