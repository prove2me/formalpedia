-- Prove2me | solution 1 for OAI.RuledApproximation.local_finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:42:18.391876+00:00
-- url     : https://prove2.me/submissions/3f41b322-e8d5-4743-b515-b0de22e0ab35

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/LocalApproximation.lean:L55-L89
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.local_finite_certificate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Theorems.Thm_OAI_RuledApproximation_finite_weighted_grid_outer

-- ---- from OAI.Geometry.RuledCovering.LocalApproximation ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The nonlinear local producer. Unlike tilting a continuum of lines, it produces a
finite set of intercept centers covering every label and every time simultaneously. -/
theorem local_finite_certificate {K U : Set Parameter} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (v : Parameter → Parameter)
    (A : Parameter →L[ℝ] Parameter) {L R delta : ℝ}
    (hL : 0 ≤ L) (hdelta : 0 ≤ delta) (hmodel : LatticeModel A L R)
    (hrem : ∀ p ∈ U, ∀ b ∈ U,
      ‖v p - v b - A (p - b)‖ ≤ delta * ‖p - b‖)
    {F : Parameter → ℝ} (hF : Continuous F) (hFpos : ∀ p, 0 ≤ F p)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : Set Parameter, S.Finite ∧ S ⊆ U ∧
      (∀ p ∈ K, ∀ r : ℝ, |r| ≤ L → ∃ b ∈ S,
        ‖p + r • v p - (b + r • v b)‖ ≤ (1 / 2 + L * delta * R) / n) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨n, hn, S, hSfinite, hSU, hretain, hcost⟩ :=
    (finite_weighted_grid_outer hK hU hKU hF hFpos R heps).exists
  refine ⟨n, hn, S, hSfinite, fun b hb => (hSU hb).1, ?_, hcost⟩
  intro p hp r hr
  obtain ⟨b, hbgrid, hbp, hlin⟩ := hmodel n hn p r hr
  have hbS := hretain b hbgrid ⟨p, hp, hbp⟩
  have hbp' : ‖p - b‖ ≤ R / n := by simpa [dist_eq_norm, norm_sub_rev] using hbp
  have herr := hrem p (hKU hp) b (hSU hbS).1
  refine ⟨b, hbS, ?_⟩
  calc
    ‖p + r • v p - (b + r • v b)‖ =
        ‖(p - b + r • A (p - b)) + r • (v p - v b - A (p - b))‖ := by
          congr 1
          module
    _ ≤ ‖p - b + r • A (p - b)‖ + ‖r • (v p - v b - A (p - b))‖ := norm_add_le _ _
    _ ≤ 1 / (2 * n) + L * (delta * (R / n)) := by
      apply add_le_add hlin
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_left hbp' hdelta)) hL)
    _ = (1 / 2 + L * delta * R) / n := by ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.local_finite_certificate := @_root_.OAI.RuledApproximation.local_finite_certificate
