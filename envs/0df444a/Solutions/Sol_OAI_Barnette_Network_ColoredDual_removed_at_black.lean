-- Prove2me | solution 1 for OAI.Barnette.Network.ColoredDual.removed_at_black
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:35:28.561985+00:00
-- url     : https://prove2.me/submissions/236db8a3-881c-47e0-b955-a5d11c974b71

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Matching.lean:L413-L446
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.ColoredDual.removed_at_black. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching

-- ---- from OAI.Combinatorics.Hamiltonian.Matching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)
end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V A : Type*} (Q : Network V A)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
lemma qLabel_black (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    N.blackEndpoint M.black (M.qLabel P t) = t.val :=
  N.blackEndpoint_eq M.black M.coloring t.property.1
    ((N.mem_star _ _).mp ((M.face t.val).side_mem D _ _))

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (D : Network V E)

lemma Triangle.other_root_sides {S : Finset E} (t : D.Triangle S) (i : Fin 3) {e : E}
    (he : e ∈ S) :
    (∃ j : Fin 2, t.side D (ColoredDual.rootStart i j) (i+2) = e) ↔ e ≠ t.edge i := by
  have he' := he
  rw [← t.edge_range] at he'
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he'
  have hh : ∀ i k : Fin 3,
      (∃ j : Fin 2, (if i+2 = ColoredDual.rootStart i j+1 then ColoredDual.rootStart i j else i+2) = k) ↔ k ≠ i := by decide
  have hs (a b : Fin 3) : t.side D a b = t.edge (if b = a+1 then a else b) := by
    unfold Triangle.side; split_ifs <;> rfl
  simp only [hs, ne_eq, t.edge_injective.eq_iff]
  exact hh i k

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
lemma removed_at_black (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (v : V) (hv : M.black v) {e : E} (he : e ∈ N.star v) :
    (e ∈ M.removed P i ↔
      if h : v = root then e ≠ (M.face root).edge i else e = M.qLabel P ⟨v,hv,h⟩) := by
  have hb : N.blackEndpoint M.black e = v := N.blackEndpoint_eq M.black M.coloring hv ((N.mem_star _ _).mp he)
  by_cases hh : v = root
  · clear hb
    subst v
    simp only
    have hb : N.blackEndpoint M.black e = root := N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp he)
    constructor
    · intro hmem
      obtain ⟨t|j,_,ht⟩ := Finset.mem_image.mp hmem
      · have hbr : (t : V) = root := (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) ht).trans hb)
        exact (t.property.2 hbr).elim
      · exact ((M.face root).other_root_sides D i he).mp ⟨j,ht⟩
    · intro hne
      obtain ⟨j,hj⟩ := ((M.face root).other_root_sides D i he).mpr hne
      exact Finset.mem_image.mpr ⟨Sum.inr j,Finset.mem_univ _,hj⟩
  · simp only [dite_eq_right hh]
    constructor
    · intro hmem
      obtain ⟨t|j,_,ht⟩ := Finset.mem_image.mp hmem
      · have htv : t.val = v := (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) ht).trans hb)
        have ht' : t = ⟨v,hv,hh⟩ := Subtype.ext htv
        change M.qLabel P t = e at ht
        rw [ht'] at ht
        exact ht.symm
      · have hbr : N.blackEndpoint M.black (M.augLabel P i (.inr j)) = root :=
          N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp ((M.face root).side_mem D _ _))
        exact (hh (hb.symm.trans ((congrArg (N.blackEndpoint M.black) ht).symm.trans hbr))).elim
    · intro heq
      exact Finset.mem_image.mpr ⟨Sum.inl ⟨v,hv,hh⟩,Finset.mem_univ _,heq.symm⟩

end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual
open scoped Classical
open Barnette.TriangleSystem


theorem solution : type_of% @_root_.OAI.Barnette.Network.ColoredDual.removed_at_black := @_root_.OAI.Barnette.Network.ColoredDual.removed_at_black
