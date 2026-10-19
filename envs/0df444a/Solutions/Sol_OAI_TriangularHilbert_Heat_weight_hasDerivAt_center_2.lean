-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.weight_hasDerivAt_center
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:58:41.605987+00:00
-- url     : https://prove2.me/submissions/1e8eeaa2-2a0f-4930-83f6-ce3ab87ef8ef

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Gaussian.lean:L37-L51
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.weight_hasDerivAt_center. The node keeps its source
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

theorem weight_hasDerivAt_center (h u p σ : ℝ) (_hσ : 0 < σ) :
    HasDerivAt (fun q => weight h u q σ) (score u p σ * weight h u p σ) p := by
  have hexp : HasDerivAt (fun q : ℝ => -(u - q)^2 / (2 * σ)) ((u - p) / σ) p := by
    convert! ((((hasDerivAt_const p u).sub (hasDerivAt_id p)).pow 2).neg.div_const
      (2 * σ)) using 1
    dsimp
    ring
  have ht := ((Real.hasDerivAt_exp _).comp p hexp).const_mul
    (h * (Real.sqrt (2 * Real.pi * σ))⁻¹)
  convert! ht using 1
  · ext q
    simp only [weight, density, Function.comp_apply]
    ring
  · simp only [score, weight, density]
    ring

end TriangularHilbert.Heat
end
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.weight_hasDerivAt_center := @_root_.OAI.TriangularHilbert.Heat.weight_hasDerivAt_center
