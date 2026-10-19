-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.weight_hasDerivAt_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:00:15.835296+00:00
-- url     : https://prove2.me/submissions/d64e480e-0dbe-4337-83dc-8fc0a60e4c57

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Gaussian.lean:L76-L91
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.weight_hasDerivAt_variance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian

-- ---- from OAI.Analysis.TriangularHilbert.Gaussian ----
namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

theorem density_normalization_hasDerivAt (σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => (Real.sqrt (2 * Real.pi * s))⁻¹)
      (-((Real.sqrt (2 * Real.pi * σ))⁻¹) / (2 * σ)) σ := by
  have hpos : 0 < 2 * Real.pi * σ := by positivity
  have hspos : 0 < Real.sqrt (2 * Real.pi * σ) := Real.sqrt_pos.2 hpos
  have ht := ((Real.hasDerivAt_sqrt hpos.ne').comp σ
    ((hasDerivAt_id σ).const_mul (2 * Real.pi))).inv hspos.ne'
  convert! ht using 1
  dsimp
  field_simp
  nlinarith [Real.sq_sqrt hpos.le]

theorem weight_hasDerivAt_variance (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => weight h u p s)
      ((1 / 2 : ℝ) * (score u p σ ^ 2 - σ⁻¹) * weight h u p σ) σ := by
  have hexp : HasDerivAt (fun s : ℝ => -(u-p)^2 / (2*s))
      ((u-p)^2 / (2*σ^2)) σ := by
    convert! (hasDerivAt_const σ (-(u-p)^2)).div
      ((hasDerivAt_id σ).const_mul 2) (by positivity : 2*σ ≠ 0) using 1
    dsimp
    ring
  have ht := ((density_normalization_hasDerivAt σ hσ).mul
    ((Real.hasDerivAt_exp _).comp σ hexp)).const_mul h
  convert! ht using 1
  unfold score weight density
  dsimp
  field_simp
  ring

end TriangularHilbert.Heat
end
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.weight_hasDerivAt_variance := @_root_.OAI.TriangularHilbert.Heat.weight_hasDerivAt_variance
