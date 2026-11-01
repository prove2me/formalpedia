-- Prove2me | solution 1 for Grunbaum2003.ray_oracle_face_lattice_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:28:42.142293+00:00
-- url     : https://prove2.me/submissions/666b3e55-8a7d-4c73-80a3-0cb1ab702c52
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
import Theorems.Thm_Grunbaum2003_rayMachine_halt_unique_and_output_iso_iff
import Theorems.Thm_Grunbaum2003_exists_ray_oracle_program_up_to_orderIso

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Gritzmann–Klee–Westwater ray-oracle reconstruction (Grünbaum 2003, §3.6, pp. 52b–52c):
for `0 < d`, there exists a ray-machine program that reconstructs the face lattice of any
`d`-polytope `P` with `0 ∈ interior P` within the Gritzmann–Klee–Westwater query bound. -/
theorem ray_oracle_face_lattice_reconstruction_sol (d : ℕ) (hd : 0 < d) :
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
  obtain ⟨program, hProg⟩ := exists_ray_oracle_program_up_to_orderIso d hd
  refine ⟨program, ?_⟩
  intro P hP h0 oracle hOracle
  obtain ⟨t, c, P', hRun, hHalt, hQueries, hOut', hIso⟩ :=
    hProg P hP h0 oracle hOracle
  refine ⟨t, c, hRun, hHalt, hQueries, ?_⟩
  exact (rayMachine_halt_unique_and_output_iso_iff.2 P' P c hOut').mpr hIso

end Grunbaum2003

theorem solution (d : ℕ) (hd : 0 < d) :
    ∃ program : List Grunbaum2003.RayInstruction,
      ∀ P : Set (Fin d → ℝ), Grunbaum2003.IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), Grunbaum2003.IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : Grunbaum2003.RayConfiguration),
            Grunbaum2003.rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ Grunbaum2003.faceCount P 0 +
              (d - 1) * (Grunbaum2003.faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * Grunbaum2003.faceCount P (d - 1) ∧
            Grunbaum2003.IsRayFaceLatticeOutput P c :=
  Grunbaum2003.ray_oracle_face_lattice_reconstruction_sol d hd
