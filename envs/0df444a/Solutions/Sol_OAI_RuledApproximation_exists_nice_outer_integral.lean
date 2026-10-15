-- Prove2me | solution 1 for OAI.RuledApproximation.exists_nice_outer_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:32:49.131883+00:00
-- url     : https://prove2.me/submissions/1b89528a-d1f6-49b1-ad92-f7cb0ef3be41

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/OuterApproximation.lean:L28-L67
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.exists_nice_outer_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Theorems.Thm_OAI_RuledApproximation_inter_reciprocal_cthickening

-- ---- from OAI.Geometry.RuledCovering.OuterApproximation ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Small open outer neighborhoods, not regularity of the label boundary, justify the weighted
lattice count for arbitrary compact label sets. -/
theorem exists_nice_outer_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [SFinite (volume : Measure E)]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : E → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ S : Set E, IsOpen S ∧ Bornology.IsBounded S ∧ K ⊆ S ∧ S ⊆ U ∧
      volume (frontier S) = 0 ∧ (∫ x in S, F x) < (∫ x in K, F x) + eps := by
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hR : ∀ n, 0 < R n := fun n => by dsimp [R]; positivity
  have hRlim : Tendsto R atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let K' : ℕ → Set E := fun n => cthickening (R n) K
  have hK' : ∀ n, IsCompact (K' n) := fun _ => hK.cthickening
  have hanti : Antitone K' := by
    intro n m hnm
    apply cthickening_mono _ K
    dsimp [R]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hInt : Tendsto (fun n => ∫ x in K' n, F x) atTop (𝓝 (∫ x in K, F x)) := by
    have ht := tendsto_setIntegral_of_antitone (μ := volume)
      (fun n => (hK' n).measurableSet) hanti
      ⟨0, hF.continuousOn.integrableOn_compact (μ := volume) (hK' 0)⟩
    rwa [show (⋂ n, K' n) = K from inter_reciprocal_cthickening K hK.isClosed] at ht
  obtain ⟨d, hd, hdU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hevent : ∀ᶠ n in atTop, (∫ x in K' n, F x) < (∫ x in K, F x) + eps ∧ R n < d :=
    (hInt.eventually (Iio_mem_nhds (lt_add_of_pos_right _ heps))).and
      (hRlim.eventually (Iio_mem_nhds hd))
  obtain ⟨n, hnInt, hnd⟩ := hevent.exists
  obtain ⟨r, hr, hrnull⟩ := exists_null_frontier_thickening volume K (hR n)
  refine ⟨thickening r K, isOpen_thickening, hK.isBounded.thickening,
    self_subset_thickening hr.1 K, ?_, hrnull, ?_⟩
  · exact (thickening_subset_cthickening r K).trans
      ((cthickening_mono (hr.2.le.trans hnd.le) K).trans hdU)
  · have hsub : thickening r K ⊆ K' n :=
      (thickening_subset_cthickening r K).trans (cthickening_mono hr.2.le K)
    exact (setIntegral_mono_set
      (hF.continuousOn.integrableOn_compact (μ := volume) (hK' n))
      (.of_forall hFpos) (.of_forall hsub)).trans_lt hnInt

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.exists_nice_outer_integral := @_root_.OAI.RuledApproximation.exists_nice_outer_integral
