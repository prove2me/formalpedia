-- Prove2me | solution 1 for OAI.Barnette.BranchPartition.quotient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:22:06.676754+00:00
-- url     : https://prove2.me/submissions/f5c8460c-0f8a-4a41-a3d4-563660f24b72

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/BranchPartition.lean:L100-L117
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.BranchPartition.quotient. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorModel

-- ---- from OAI.Combinatorics.Hamiltonian.BranchPartition ----
namespace OAI

/-! Extending disjoint connected branches to a connected vertex partition. -/

namespace Barnette
noncomputable section
open scoped Classical

namespace BranchPartition
variable {V W : Type*} [Fintype V] [Fintype W] [Nonempty V]
  (H : SimpleGraph W)

omit [Fintype V] [Fintype W] [Nonempty V] in

theorem quotient (B : V → Set W)
    (hB : ∀ v, (H.induce (B v)).Connected)
    (hd : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hcover : ∀ w, ∃ v, w ∈ B v) :
    ∃ q : W → V, Function.Surjective q ∧ (∀ w v, q w = v ↔ w ∈ B v) := by
  choose q hq using hcover
  have he (w : W) (v : V) : q w = v ↔ w ∈ B v := by
    constructor
    · intro hv; exact hv ▸ hq w
    · intro hw
      by_contra hne
      exact Set.disjoint_left.mp (hd (q w) v hne) (hq w) hw
  refine ⟨q, ?_, he⟩
  intro v
  obtain ⟨w⟩ := (hB v).nonempty
  exact ⟨w.val, (he w.val v).mpr w.property⟩

end BranchPartition
end
end Barnette

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.BranchPartition
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.BranchPartition.quotient := @_root_.OAI.Barnette.BranchPartition.quotient
