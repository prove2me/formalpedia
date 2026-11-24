-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_restart_clock_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:01.869595+00:00
-- url     : https://prove2.me/submissions/bc2f7fbb-96b5-4888-bb66-f546dfa70c9b

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Tactic.Positivity
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) () ≤ ((l-t : ℝ≥0) : WithTop ℝ≥0) := by
  intro Ω X ω y t l ht hl
  let S : Set (WithTop ℝ≥0) := {r | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = r ∧ y + X u ω < 0}
  let R : Set (WithTop ℝ≥0) := {r | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = r ∧ y + X (t+u) ω < 0}
  change sInf S = (t : WithTop ℝ≥0) at ht
  change sSup S = (l : WithTop ℝ≥0) at hl
  change sSup R ≤ ((l-t : ℝ≥0) : WithTop ℝ≥0)
  apply sSup_le
  rintro r ⟨u,hu,rfl,hneg⟩
  have hm : (↑(t+u) : WithTop ℝ≥0) ∈ S :=
    ⟨t+u, by positivity, rfl, hneg⟩
  have hle := le_sSup hm
  rw [hl] at hle
  exact WithTop.coe_le_coe.mpr (le_tsub_of_add_le_left (WithTop.coe_le_coe.mp hle))
