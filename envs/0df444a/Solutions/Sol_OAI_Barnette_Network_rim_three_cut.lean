-- Prove2me | solution 1 for OAI.Barnette.Network.rim_three_cut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:16:32.840529+00:00
-- url     : https://prove2.me/submissions/62eb8019-3793-41f3-ab67-a1ddbe0c95cb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Contraction.lean:L345-L359
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.rim_three_cut. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_rim_cut_count

-- ---- from OAI.Combinatorics.Hamiltonian.Forest ----
namespace OAI

/-! Common-phase nonvanishing and forest extraction from actual states. -/

namespace Barnette
noncomputable section
open scoped Classical

namespace TriangleSystem.Pair
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

variable [Fintype A]

end TriangleSystem.Pair
end
end Barnette
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {F : Type*} [Fintype F]
omit [Fintype E] [Fintype F] in
lemma componentMap_surjective (H : Network F E) : Function.Surjective H.componentMap := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h f => exact ⟨f, rfl⟩

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Contraction ----
namespace OAI

/-! Contraction and deletion of finite oriented dual networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma regionShore_nonempty (U : Finset F) (q : N.Regions D U) :
    (N.regionShore D U q).Nonempty := by
  obtain ⟨v,hv⟩ := (N.regions D U).componentMap_surjective q
  exact ⟨v,(N.mem_regionShore D U q v).mpr hv⟩

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma cut_le_rim (U : Finset F) (q : N.Regions D U) :
    (N.cut (N.regionShore D U q)).card ≤ N.rim D U q := by
  rw [N.rim_cut_count]
  omega

omit [Fintype F] in
lemma rim_of_shore_univ (U : Finset F) (q : N.Regions D U)
    (hq : N.regionShore D U q = Finset.univ) :
    N.rim D U q = 2 * (D.inducedEdges U).card := by
  simp [rim,hq,Nat.mul_comm]

omit [Fintype F] in
lemma rim_three_cut (hN : N.ThreeEdgeConnected) (U : Finset F)
    (_hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) (hq : N.rim D U q = 3) :
    (N.cut (N.regionShore D U q)).card = 3 := by
  have hproper : N.regionShore D U q ≠ Finset.univ := by
    intro he
    have hh := N.rim_of_shore_univ D U q he
    omega
  have hAc : (N.regionShore D U q)ᶜ.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hproper ((Finset.compl_eq_empty_iff _).mp he)
  have hl := hN _ (N.regionShore_nonempty D U q) hAc
  have hu := N.cut_le_rim D U q
  omega

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.rim_three_cut := @_root_.OAI.Barnette.Network.rim_three_cut
