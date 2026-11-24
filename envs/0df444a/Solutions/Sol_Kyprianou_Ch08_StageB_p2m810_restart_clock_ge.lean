-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_restart_clock_ge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:48:41.44926+00:00
-- url     : https://prove2.me/submissions/4977ff5f-723e-439d-98c9-a1c80f0ecd01

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_clock_order
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (y : ℝ) (t l : ℝ≥0),
      tauMinus (shifted X y) 0 ω = (t : WithTop ℝ≥0) →
      lastExitShifted X y ω = (l : WithTop ℝ≥0) →
      ((l-t : ℝ≥0) : WithTop ℝ≥0) ≤ lastNegativeVisit (fun s (_ : Unit) => y + X (t+s) ω) () := by
  intro Ω X ω y t l ht hl
  have htl := p2m810_restart_clock_order Ω X ω y t l ht hl
  let S : Set (WithTop ℝ≥0) := {r | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = r ∧ y + X u ω < 0}
  let R : Set (WithTop ℝ≥0) := {r | ∃ u : ℝ≥0,
    0 < u ∧ (u : WithTop ℝ≥0) = r ∧ y + X (t+u) ω < 0}
  change sInf S = (t : WithTop ℝ≥0) at ht
  change sSup S = (l : WithTop ℝ≥0) at hl
  change ((l-t : ℝ≥0) : WithTop ℝ≥0) ≤ sSup R
  have hbound : sSup S ≤ (t : WithTop ℝ≥0) + sSup R := by
    apply sSup_le
    rintro r ⟨u,hu,rfl,hneg⟩
    have htu : t ≤ u := by
      have hle := sInf_le (show (u : WithTop ℝ≥0) ∈ S from ⟨u,hu,rfl,hneg⟩)
      rw [ht] at hle
      exact WithTop.coe_le_coe.mp hle
    rcases eq_or_lt_of_le htu with he | hs
    · subst u
      exact le_add_of_nonneg_right (zero_le)
    · have hv : (↑(u-t) : WithTop ℝ≥0) ∈ R :=
        ⟨u-t, tsub_pos_of_lt hs, rfl, by rwa [add_tsub_cancel_of_le htu]⟩
      have he : (u : WithTop ℝ≥0) =
          (t : WithTop ℝ≥0) + (↑(u-t) : WithTop ℝ≥0) := by
        rw [← WithTop.coe_add, add_tsub_cancel_of_le htu]
      rw [he]
      exact add_le_add_right (le_sSup hv) _
  rw [hl] at hbound
  have he : (l : WithTop ℝ≥0) =
      (t : WithTop ℝ≥0) + (↑(l-t) : WithTop ℝ≥0) := by
    rw [← WithTop.coe_add, add_tsub_cancel_of_le htl]
  rw [he] at hbound
  exact (WithTop.add_le_add_iff_left (WithTop.coe_ne_top)).mp hbound
