-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.weight_hasDerivAt_center
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:28:24.552773+00:00
-- url     : https://prove2.me/submissions/dfc4606f-29ee-47f8-832a-a2175ae49d31

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution (h u p σ : ℝ) (_hσ : 0 < σ) :
    HasDerivAt (fun q => weight h u q σ) (score u p σ * weight h u p σ) p := by
  have hσ0 : σ ≠ 0 := ne_of_gt _hσ
  unfold weight density score
  have h1 : HasDerivAt (fun q => -(u - q) ^ 2 / (2 * σ)) ((u - p) / σ) p := by
    refine ((((hasDerivAt_id p).const_sub u).pow 2).neg.div_const (2 * σ)).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  refine ((h1.exp.const_mul ((Real.sqrt (2 * Real.pi * σ))⁻¹)).const_mul h).congr_deriv ?_
  ring

