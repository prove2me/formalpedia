-- Prove2me | solution 1 for Grunbaum2003.exists_ray_oracle_program_up_to_orderIso
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:11:53.923204+00:00
-- url     : https://prove2.me/submissions/3fb2f8fa-adf0-4520-8109-727db7df007a

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Order.Hom.Basic

import Theorems.Thm_Grunbaum2003_ray_oracle_face_lattice_reconstruction_one_dim
import Theorems.Thm_Grunbaum2003_ray_oracle_face_lattice_reconstruction_ge_two
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators
open Grunbaum2003

theorem solution (d : ℕ) (hd : 0 < d) :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin d → ℝ), IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
        ∀ oracle : (Fin d → ℝ) → (Fin d → ℝ), IsPolytopeRayOracle P oracle →
          ∃ (t : ℕ) (c : RayConfiguration) (P' : Set (Fin d → ℝ)),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧
            c.queries ≤ faceCount P 0 + (d - 1) * (faceCount P (d - 1)) ^ 2 +
              (5 * d - 4) * faceCount P (d - 1) ∧
            IsRayFaceLatticeOutput P' c ∧
            Nonempty (PolytopeFace P' ≃o PolytopeFace P) := by
  by_cases hd1 : d = 1
  · subst d
    obtain ⟨program, hProgram⟩ := ray_oracle_face_lattice_reconstruction_one_dim
    refine ⟨program, ?_⟩
    intro P hP hZero oracle hOracle
    obtain ⟨t, c, hRun, hHalt, hQueries, hOutput⟩ := hProgram P hP oracle
    refine ⟨t, c, P, hRun, hHalt, ?_, hOutput, ⟨OrderIso.refl _⟩⟩
    rw [hQueries]
    exact Nat.zero_le _
  · have hd2 : 2 ≤ d := by omega
    obtain ⟨program, hProgram⟩ := ray_oracle_face_lattice_reconstruction_ge_two d hd2
    refine ⟨program, ?_⟩
    intro P hP hZero oracle hOracle
    obtain ⟨t, c, hRun, hHalt, hQueries, hOutput⟩ := hProgram P hP hZero oracle hOracle
    exact ⟨t, c, P, hRun, hHalt, hQueries, hOutput, ⟨OrderIso.refl _⟩⟩

