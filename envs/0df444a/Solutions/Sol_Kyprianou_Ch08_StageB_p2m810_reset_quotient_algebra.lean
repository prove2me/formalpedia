-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_reset_quotient_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:29:46.999866+00:00
-- url     : https://prove2.me/submissions/ee3b8ead-9765-4993-8d0e-231061143855


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit renewal reduction. -/
theorem solution :
    ∀ (wx w0 wb zx z0 zb : ℝ),
      0 < w0 → 0 < wb → z0 - zb * w0 / wb < 1 →
      wx / wb + (zx - zb * wx / wb) *
        ((w0 / wb) / (1 - (z0 - zb * w0 / wb))) =
        (zx - wx * ((z0 - 1) / w0)) /
          (zb - wb * ((z0 - 1) / w0)) := by
  intro wx w0 wb zx z0 zb hw0 hwb hb
  let d := wb - wb*z0 + zb*w0
  have hd : 0 < d := by
    have h : z0-1 < zb*w0/wb := by linarith
    have h' := (lt_div_iff₀ hwb).1 h
    dsimp [d]
    linarith
  have h1 : 1 - (z0 - zb*w0/wb) = d/wb := by
    dsimp [d]
    field_simp [hwb.ne'] <;> ring
  have h2 : zb - wb*((z0-1)/w0) = d/w0 := by
    dsimp [d]
    field_simp [hw0.ne'] <;> ring
  rw [h1,h2]
  field_simp [hw0.ne', hwb.ne', hd.ne'] <;> ring
