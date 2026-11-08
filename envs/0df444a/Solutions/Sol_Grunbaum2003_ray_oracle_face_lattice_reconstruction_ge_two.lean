-- Prove2me | solution 1 for Grunbaum2003.ray_oracle_face_lattice_reconstruction_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T19:08:58.838676+00:00
-- url     : https://prove2.me/submissions/0a1d878c-a473-4e66-bf1d-cd4dd253678d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Theorems.Thm_Grunbaum2003_polytope_normalized_halfspace_presentation_and_facet_lower_bound
import Theorems.Thm_Grunbaum2003_repaired_ray_query_budget_bound
import Theorems.Thm_Grunbaum2003_rayMachine_relocate_and_section_query_adapter
import Theorems.Thm_Grunbaum2003_rayMachine_inner_simplex_and_signed_direction_program
import Theorems.Thm_Grunbaum2003_rayOracle_local_sector_and_known_facet_exclusion
import Theorems.Thm_Grunbaum2003_rayFrame_boundary_extension_axes_and_cramer_normal
import Theorems.Thm_Grunbaum2003_rayMachine_planar_reference_walk_and_one_sided_budget
import Theorems.Thm_Grunbaum2003_ray_oracle_phased_facet_discovery_and_lattice_synthesis
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators Matrix

namespace Grunbaum2003

theorem ray_oracle_face_lattice_reconstruction_ge_two_sol (d : ℕ) (hd : 2 ≤ d) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d - 1) * (faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * faceCount P (d - 1) ∧
            IsRayFaceLatticeOutput P c := by
  have hdpos : 0 < d := by omega
  have hLocal :
      ∀ {k : ℕ} (L : Fin k → (Fin d → ℝ) →ₗ[ℝ] ℝ) (p u : Fin d → ℝ),
        (∀ j, L j p < 1) →
        let δ := ∏ j, (1 - L j p) / (1 + (1 - L j p))
        let M := 1 + ∑ j, (L j u) ^ 2
        0 < δ ∧ 0 ≤ M ∧ (∀ j, L j p ≤ 1 - δ) ∧ (∀ j, |L j u| ≤ M) :=
    fun L p u h => rayOracle_local_sector_and_known_facet_exclusion.{0}.2.2.2.1 L p u h
  obtain ⟨⟨relocateInst, relocateCfg, hRel⟩, _⟩ := rayMachine_relocate_and_section_query_adapter
  obtain ⟨_, _, _, _, _, _, innerSampleProgram, queryVector, _, _, _, _, _, _, _, hInner⟩ :=
    rayMachine_inner_simplex_and_signed_direction_program
  obtain ⟨_, frameCramerCoefficients, frameNormal, _, _, hFrameNormal, _⟩ :=
    rayFrame_boundary_extension_axes_and_cramer_normal
  obtain ⟨_, _, _, _, _, _, _, secondQueryProgram, firstMidpointProgram, referenceWalkProgram, _⟩ :=
    rayMachine_planar_reference_walk_and_one_sided_budget
  obtain ⟨program, hProg⟩ :=
    ray_oracle_phased_facet_discovery_and_lattice_synthesis d hd
      relocateInst relocateCfg (fun pre prog oracle t c => hRel d pre prog oracle t c)
      innerSampleProgram queryVector (fun oracle tape q => by
        obtain ⟨c, h1, h2, h3, h4, h5, h6, _, _, h9⟩ := hInner d hdpos oracle tape q
        exact ⟨c, h1, h2, h3, h4, h5, h6, h9⟩)
      (@frameCramerCoefficients d) (@frameNormal d) (fun v x => hFrameNormal d v x)
      hLocal
      secondQueryProgram firstMidpointProgram referenceWalkProgram
  refine ⟨program, ?_⟩
  intro P hP hZero oracle hOracle
  obtain ⟨hm, hL⟩ :=
    polytope_normalized_halfspace_presentation_and_facet_lower_bound d hdpos P hP hZero oracle hOracle
  obtain ⟨t, c, hRun, hHalt, hQueriesPhased, hOut⟩ :=
    hProg P hP hZero oracle hOracle hm hL
  have hBudget :=
    (repaired_ray_query_budget_bound d (faceCount P (d - 1)) (faceCount P 0) hd hm).2
  exact ⟨t, c, hRun, hHalt, hQueriesPhased.trans hBudget, hOut⟩

end Grunbaum2003

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ program : List Grunbaum2003.RayInstruction,
      ∀ P : Set (Fin d → ℝ), Grunbaum2003.IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), Grunbaum2003.IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : Grunbaum2003.RayConfiguration),
            Grunbaum2003.rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ Grunbaum2003.faceCount P 0 + (d - 1) * (Grunbaum2003.faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * Grunbaum2003.faceCount P (d - 1) ∧
            Grunbaum2003.IsRayFaceLatticeOutput P c :=
  Grunbaum2003.ray_oracle_face_lattice_reconstruction_ge_two_sol d hd
