-- Prove2me | solution 1 for OAI.Barnette.Network.cap_star_some
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:44:23.950238+00:00
-- url     : https://prove2.me/submissions/718f8be7-942b-4904-a66c-47f4acdb3615

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean:L169-L183
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.cap_star_some. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts

-- ---- from OAI.Combinatorics.Hamiltonian.ThreeCuts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Three-edge cuts, capped graphs, and preservation of graph properties. -/

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
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
lemma cap_star_some (A : Finset V) (v : A) :
    ((N.cap A).star (some v)).image Subtype.val = N.star v.val := by
  ext e
  simp only [Finset.mem_image,mem_star,Incident]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact hk.elim (fun h => Or.inl ((N.capMap_eq_some A _ v).mp h))
      (fun h => Or.inr ((N.capMap_eq_some A _ v).mp h))
  · intro he
    have hm : e ∈ N.regionEdges A := (N.mem_regionEdges A e).mpr
      (he.elim (fun h => Or.inl (h ▸ v.property)) (fun h => Or.inr (h ▸ v.property)))
    refine ⟨⟨e,hm⟩,?_,rfl⟩
    exact he.elim (fun h => Or.inl ((N.capMap_eq_some A _ v).mpr h))
      (fun h => Or.inr ((N.capMap_eq_some A _ v).mpr h))

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.cap_star_some := @_root_.OAI.Barnette.Network.cap_star_some
