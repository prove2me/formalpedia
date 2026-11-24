-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_restart_clock_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:47:45.976667+00:00
-- url     : https://prove2.me/submissions/a481ee06-5c72-43a0-80d3-9d93c2fa9a55

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      t ≤ l := by
  intro Ω X ω y t l ht hl
  let S : Set (WithTop ℝ≥0) := {r | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = r ∧ y + X u ω < 0}
  let R : Set (WithTop ℝ≥0) := {r | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = r ∧ y + X (t+u) ω < 0}
  change sInf S = (t : WithTop ℝ≥0) at ht
  change sSup S = (l : WithTop ℝ≥0) at hl
  have hS : S.Nonempty := by
    have hh : sInf S < (⊤ : WithTop ℝ≥0) := by rw [ht]; exact WithTop.coe_lt_top _
    obtain ⟨r,hr,_⟩ := sInf_lt_iff.mp hh
    exact ⟨r,hr⟩
  have htl : t ≤ l := by
    obtain ⟨r,hr⟩ := hS
    have hh := (sInf_le hr).trans (le_sSup hr)
    rw [ht, hl] at hh
    exact WithTop.coe_le_coe.mp hh
  exact htl
