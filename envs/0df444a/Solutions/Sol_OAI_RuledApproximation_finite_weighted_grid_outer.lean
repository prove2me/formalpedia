-- Prove2me | solution 1 for OAI.RuledApproximation.finite_weighted_grid_outer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:34:05.705984+00:00
-- url     : https://prove2.me/submissions/25cbf553-4169-49e7-b751-e833cffdbb20

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/OuterApproximation.lean:L80-L112
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.finite_weighted_grid_outer. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Theorems.Thm_OAI_RuledApproximation_exists_nice_outer_integral

-- ---- from OAI.Geometry.RuledCovering.OuterApproximation ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma finite_inter_coordinateGrid {S : Set (Fin 2 → ℝ)} (hS : Bornology.IsBounded S)
    {n : ℕ} (hn : n ≠ 0) : (S ∩ coordinateGrid n).Finite := by
  classical
  unfold coordinateGrid
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (Nat.cast_ne_zero.mpr hn))]
  exact ZSpan.setFinite_inter _ hS

/-- A finite lattice retained around any compact label set has arbitrarily accurate weighted
cost. The finite set is the intersection with a fixed regular outer neighborhood, so no
assumption on the boundary or positive area of `K` occurs here. -/
theorem finite_weighted_grid_outer {K U : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : (Fin 2 → ℝ) → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    (R : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ S : Set (Fin 2 → ℝ), S.Finite ∧
      S ⊆ U ∩ coordinateGrid n ∧
      (∀ b ∈ coordinateGrid n, (∃ p ∈ K, dist b p ≤ R / n) → b ∈ S) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by
  obtain ⟨O, hOo, hOb, hKO, hOU, hOf, hOI⟩ :=
    exists_nice_outer_integral hK hU hKU hF hFpos (half_pos heps)
  obtain ⟨d, hd, hdO⟩ := hK.exists_cthickening_subset_open hOo hKO
  have hsum := tendsto_tsum_div_pow_atTop_integral O F hF hOb hOo.measurableSet hOf
  have hcost : ∀ᶠ n : ℕ in atTop,
      (∑' b : ↑(O ∩ coordinateGrid n), F b) / (n : ℝ) ^ 2 <
        (∫ p in O, F p) + eps / 2 := by
    simpa only [coordinateGrid, Fintype.card_fin] using
      hsum.eventually (Iio_mem_nhds (lt_add_of_pos_right _ (half_pos heps)))
  have hsmall : ∀ᶠ n : ℕ in atTop, R / (n : ℝ) < d := by
    have ht : Tendsto (fun n : ℕ => R / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun n : ℕ => R * (n : ℝ)⁻¹) atTop (𝓝 (R * 0)))
    exact ht.eventually (Iio_mem_nhds hd)
  filter_upwards [eventually_gt_atTop 0, hcost, hsmall] with n hn hcost hnsmall
  refine ⟨hn, O ∩ coordinateGrid n, finite_inter_coordinateGrid hOb hn.ne',
    Set.inter_subset_inter_left _ hOU, ?_, ?_⟩
  · intro b hb ⟨p, hp, hbp⟩
    exact ⟨hdO ((thickening_subset_cthickening d K)
      (mem_thickening_iff.mpr ⟨p, hp, hbp.trans_lt hnsmall⟩)), hb⟩
  · linarith

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.finite_weighted_grid_outer := @_root_.OAI.RuledApproximation.finite_weighted_grid_outer
