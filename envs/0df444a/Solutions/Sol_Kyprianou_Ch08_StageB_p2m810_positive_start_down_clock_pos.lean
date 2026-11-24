-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_positive_start_down_clock_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:01:36.93471+00:00
-- url     : https://prove2.me/submissions/47fa7e53-0f8f-4bc3-9320-653bf87c245a

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (y : ℝ) (hy : 0 < y) (h0 : f 0 = 0)
    (hc : ContinuousWithinAt f (Ici 0) 0) :
    0 < tauMinus (shifted (fun t (_ : Unit) => f t) y) 0 () := by
  have hmem : f 0 ∈ Ioi (-y) := by rw [h0]; simp; linarith
  obtain ⟨b,hb,hs⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hc (Ioi_mem_nhds hmem))
  have hle : (b : WithTop ℝ≥0) ≤
      tauMinus (shifted (fun t (_ : Unit) => f t) y) 0 () := by
    unfold tauMinus
    apply le_sInf
    rintro _ ⟨u,hu,rfl,hneg⟩
    apply WithTop.coe_le_coe.mpr
    by_contra! hub
    have hh := hs ⟨zero_le,hub⟩
    change -y < f u at hh
    change y + f u < 0 at hneg
    linarith
  exact (WithTop.coe_lt_coe.mpr hb).trans_le hle
