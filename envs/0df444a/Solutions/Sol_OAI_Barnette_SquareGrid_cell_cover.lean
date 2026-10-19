-- Prove2me | solution 1 for OAI.Barnette.SquareGrid.cell_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:10:44.080945+00:00
-- url     : https://prove2.me/submissions/d713e808-7c9b-4c8c-ae43-1fdfdc4fbcaf

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/SquareGrid.lean:L34-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.SquareGrid.cell_cover. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.SquareGrid ----
namespace OAI

/-! Ordinary square cells and connected finite lattice corridors. -/

namespace Barnette.SquareGrid

noncomputable section

theorem cell_cover {δ : ℝ} (hδ : 0 < δ) (p : ℝ × ℝ) : ∃ z, p ∈ cell δ z := by
  refine ⟨(⌊p.1 / δ⌋, ⌊p.2 / δ⌋), ?_⟩
  constructor
  · constructor
    · have h := (le_div_iff₀ hδ).mp (Int.floor_le (p.1 / δ))
      simpa only [mul_comm] using h
    · have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (p.1 / δ))
      exact le_of_lt (by simpa only [mul_comm] using h)
  · constructor
    · have h := (le_div_iff₀ hδ).mp (Int.floor_le (p.2 / δ))
      simpa only [mul_comm] using h
    · have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (p.2 / δ))
      exact le_of_lt (by simpa only [mul_comm] using h)

end
end Barnette.SquareGrid
namespace Barnette.SquareGrid

noncomputable section

end
end Barnette.SquareGrid

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.SquareGrid


theorem solution : type_of% @_root_.OAI.Barnette.SquareGrid.cell_cover := @_root_.OAI.Barnette.SquareGrid.cell_cover
