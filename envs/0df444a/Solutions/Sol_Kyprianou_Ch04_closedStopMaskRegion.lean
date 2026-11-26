-- Prove2me | solution 1 for Kyprianou.Ch04.closedStopMaskRegion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:26:41.317879+00:00
-- url     : https://prove2.me/submissions/49418887-0d7f-46f4-97cc-1e9a7f81573a

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- A deterministic horizon intersected with a closed stop is the clipped horizon. -/
theorem solution (tau : WithTop NNReal) (t c : NNReal)
    (hc : (c : WithTop NNReal) = min tau (t : WithTop NNReal)) (s : ℝ) :
    (s ∈ Set.Icc (0 : ℝ) (t : ℝ) ∧ (s.toNNReal : WithTop NNReal) ≤ tau) ↔
      s ∈ Set.Icc (0 : ℝ) (c : ℝ) := by
  have hct : c ≤ t := WithTop.coe_le_coe.mp (hc.trans_le (min_le_right _ _))
  constructor
  · rintro ⟨hs,hsτ⟩
    refine ⟨hs.1,Real.toNNReal_le_iff_le_coe.mp (WithTop.coe_le_coe.mp ?_)⟩
    rw [hc]
    exact le_min hsτ (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hs.2))
  · intro hs
    have hsc := WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hs.2)
    refine ⟨⟨hs.1,hs.2.trans (by exact_mod_cast hct)⟩,?_⟩
    rw [hc] at hsc
    exact hsc.trans (min_le_left _ _)
