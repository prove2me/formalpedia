-- Prove2me | solution 1 for OAI.Barnette.SquareGrid.cells_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:12:46.119148+00:00
-- url     : https://prove2.me/submissions/2e59ec5b-1632-4540-a014-d009826a607b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/SquareGrid.lean:L64-L77
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.SquareGrid.cells_finite. The node keeps its source
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

private theorem int_bound_of_cell {δ R : ℝ} (hδ : 0 < δ) {a : ℤ} {x : ℝ}
    (hx : -R ≤ x ∧ x ≤ R) (ha : δ * a ≤ x ∧ x ≤ δ * ((a : ℝ) + 1)) :
    -(R / δ + 1) ≤ (a : ℝ) ∧ (a : ℝ) ≤ R / δ + 1 := by
  have hu : (a : ℝ) ≤ R / δ :=
    (le_div_iff₀ hδ).mpr (by nlinarith [ha.1, hx.2])
  have hl : -R / δ ≤ (a : ℝ) + 1 :=
    (div_le_iff₀ hδ).mpr (by nlinarith [ha.2, hx.1])
  rw [neg_div] at hl
  constructor <;> linarith

theorem cells_finite {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) : (cells δ K).Finite := by
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_int_ge (R / δ + 1)
  apply ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset
  rintro z ⟨p, hp, hpK⟩
  have hp₁ : -R ≤ p.1 ∧ p.1 ≤ R := abs_le.mp ((norm_fst_le p).trans (hR p hpK))
  have hp₂ : -R ≤ p.2 ∧ p.2 ≤ R := abs_le.mp ((norm_snd_le p).trans (hR p hpK))
  obtain ⟨hz₁, hz₁'⟩ := int_bound_of_cell hδ hp₁ hp.1
  obtain ⟨hz₂, hz₂'⟩ := int_bound_of_cell hδ hp₂ hp.2
  have hb₁ : (-(N : ℝ)) ≤ z.1 ∧ (z.1 : ℝ) ≤ N := by constructor <;> linarith
  have hb₂ : (-(N : ℝ)) ≤ z.2 ∧ (z.2 : ℝ) ≤ N := by constructor <;> linarith
  exact ⟨⟨by exact_mod_cast hb₁.1, by exact_mod_cast hb₁.2⟩,
    ⟨by exact_mod_cast hb₂.1, by exact_mod_cast hb₂.2⟩⟩

end
end Barnette.SquareGrid
namespace Barnette.SquareGrid

noncomputable section

end
end Barnette.SquareGrid

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.SquareGrid


theorem solution : type_of% @_root_.OAI.Barnette.SquareGrid.cells_finite := @_root_.OAI.Barnette.SquareGrid.cells_finite
