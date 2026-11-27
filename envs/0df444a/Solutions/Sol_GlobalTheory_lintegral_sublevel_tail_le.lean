-- Prove2me | solution 1 for GlobalTheory.lintegral_sublevel_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:11.565746+00:00
-- url     : https://prove2.me/submissions/f5a07902-ec4b-4830-a15a-374bca687495

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralSublevelTailLeOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞)
    (x : Y → ℝ) (hx : Measurable x) (hg : ∫⁻ y, g y ∂μ < ⊤) (_hm : Measurable g)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  have hms : ∀ T : ℝ, MeasurableSet {y | x y ≤ -T + 1} := fun T =>
    measurableSet_le hx measurable_const
  haveI : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.ne
  have hanti : Antitone (fun n : ℕ => {y | x y ≤ -(n : ℝ) + 1}) := by
    intro a b hab y hy
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [Set.mem_setOf_eq] at hy ⊢
    linarith
  have h := tendsto_measure_iInter_atTop (μ := μ.withDensity g)
    (fun n : ℕ => (hms n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hem : (⋂ n : ℕ, {y | x y ≤ -(n : ℝ) + 1}) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - x y)
    exact ⟨n, by linarith⟩
  rw [hem, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds hε)).exists
  refine ⟨n, fun T hT => ?_⟩
  rw [← withDensity_apply _ (hms T)]
  refine le_trans (measure_mono ?_) hn
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  linarith
end GlobalTheory
