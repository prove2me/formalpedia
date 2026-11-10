-- Prove2me | solution 2 for Grunbaum2003.ray_oracle_face_lattice_reconstruction_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T08:52:59.54282+00:00
-- url     : https://prove2.me/submissions/90e3a7bc-4638-446f-bf97-41331cef42d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Grunbaum2003_ray_oracle_phased_discovery_runtime_v2

set_option autoImplicit false
open scoped Classical BigOperators
open Grunbaum2003

-- Relative reduction through the published Open V2 child.
theorem solution (d : ℕ) (hd : 2 ≤ d) :
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
  obtain ⟨program, phasePC, hprogram⟩ :=
    Grunbaum2003.ray_oracle_phased_discovery_runtime_v2 d hd
  refine ⟨program, ?_⟩
  intro P hP h0 oracle hOracle
  obtain ⟨L, V, N, boundedStart, S, C, time, state,
    hrep, hfacets, hinj, hVext, hVexposed, hVcard,
    hS0, hC0, hq0, hBN, hruns, htimes, hcompact, hsteps,
    hterminalP, hterminalC, houtput⟩ := hprogram P hP h0 oracle hOracle
  obtain ⟨n, e, vEnum, tableTime, haltTime, tableState, haltState, base,
    hTimeN, hTimeFinal, hTableRun, hTablePred, hHaltRun, hHaltPc,
    hTableQ, hHaltQ, hbound, hOutput⟩ := houtput
  exact ⟨haltTime, haltState, hHaltRun, hHaltPc, hbound, hOutput⟩
