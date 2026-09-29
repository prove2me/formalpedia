-- Prove2me | solution 1 for MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/148b65b5-eeee-5a66-85a4-519931bbbffb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  haveI : IsFiniteMeasureOnCompacts μ.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  constructor
  set c : ℝ≥0 := Measure.haarScalarFactor μ.inv μ with hc_def
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hc' : μ.inv = (c : ℝ≥0∞) • μ := by rw [hc]; rfl
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = ((c : ℝ≥0∞) ^ 2) • μ := by
    rw [← Measure.inv_def μ, hc', Measure.map_smul, ← Measure.inv_def μ, hc', smul_smul, pow_two]
  have μeq : μ = ((c : ℝ≥0∞) ^ 2) • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have h3 : (c : ℝ≥0∞) ^ 2 * μ K₀ = 1 ^ 2 * μ K₀ := by
    conv_rhs => rw [μeq]
    simp
  have hK₀ : 0 < μ (K₀ : Set G) :=
    (isOpen_interior.measure_pos μ K₀.interior_nonempty).trans_le (measure_mono interior_subset)
  have h4 : (c : ℝ≥0∞) ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj hK₀.ne' K₀.isCompact.measure_lt_top.ne).1 h3
  have h5 : (c : ℝ≥0∞) = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h4
  rw [hc', h5, one_smul]

end S_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
end P2MW
export P2MW.S_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant (solution)
