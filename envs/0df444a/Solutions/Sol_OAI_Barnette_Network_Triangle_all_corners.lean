-- Prove2me | solution 1 for OAI.Barnette.Network.Triangle.all_corners
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:20:39.62637+00:00
-- url     : https://prove2.me/submissions/8c214453-28f7-4ab3-a793-425a73d09736

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean:L140-L156
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Triangle.all_corners. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.MinorDuality ----
namespace OAI

/-! Exact duality under finite network minors. -/

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

omit [Fintype V] [Fintype F] in
lemma Triangle.all_corners {s : Finset E} (t : D.Triangle s) (U : Finset F) :
    s ⊆ D.inducedEdges U ↔ ∀ i, t.corner i ∈ U := by
  constructor
  · intro h i
    have hm : t.edge i ∈ s := by
      have hi : t.edge i ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      simpa only [t.edge_range] using hi
    have he := (D.mem_inducedEdges U _).mp (h hm)
    rcases Sym2.eq_iff.mp (t.edge_ends i) with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · exact ht ▸ he.1
    · exact hh ▸ he.2
  · intro h e he
    rw [← t.edge_range] at he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    apply (D.mem_inducedEdges U _).mpr
    rcases Sym2.eq_iff.mp (t.edge_ends i) with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> simp [ht,hh,h]

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.Triangle.all_corners := @_root_.OAI.Barnette.Network.Triangle.all_corners
