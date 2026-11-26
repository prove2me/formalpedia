-- Prove2me | solution 1 for Kyprianou.Ch04.shiftedMarkedCountExtractorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:02:28.499726+00:00
-- url     : https://prove2.me/submissions/c37c52c0-65e9-4a8e-9309-66b84a841f24

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_Kyprianou_Ch04_shiftedMarkedCountTranslationV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitTimeMeasurableV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable functional of the future increment path extracts the intrinsic marked count. -/
theorem solution (s T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ G : (NNReal → ℝ) → ENNReal, Measurable G ∧
      ∀ {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω),
      (∀ t : NNReal, ContinuousWithinAt (fun u => X u ω) (Ici t) t) →
      (∀ t : NNReal, 0 < t → Tendsto (fun u => X u ω) (𝓝[<] t) (𝓝 (L t ω))) →
      Kyprianou.Ch04.pathJumpMeasure X L ω (Ioc (s : ℝ) ((s+T : NNReal) : ℝ) ×ˢ B) =
        G (fun v : NNReal => X (s+v) ω - X s ω) := by
  obtain ⟨G,hG,hExtract⟩ :=
    AvramDividend.Classical.avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable T B hB
  refine ⟨G,hG,?_⟩
  intro Ω X L ω hR hL
  let Y (v : NNReal) := X (s+v) ω - X s ω
  have hYR (v : NNReal) : ContinuousWithinAt Y (Ici v) v := by
    have hadd : Tendsto (fun u : NNReal => s+u) (𝓝[Ici v] v) (𝓝[Ici (s+v)] (s+v)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds), ?_⟩
      filter_upwards [self_mem_nhdsWithin (a := v) (s := Ici v)] with u hu
      simpa only [mem_Ici, add_comm s] using add_le_add_left hu s
    exact ((hR (s+v)).tendsto.comp hadd).sub tendsto_const_nhds
  have hYL (v : NNReal) (hv : 0 < v) :
      Tendsto Y (𝓝[<] v) (𝓝 (L (s+v) ω - X s ω)) := by
    have hadd : Tendsto (fun u : NNReal => s+u) (𝓝[<] v) (𝓝[<] (s+v)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds), ?_⟩
      filter_upwards [self_mem_nhdsWithin (a := v) (s := Iio v)] with u hu
      simpa only [mem_Iio, add_comm s] using add_lt_add_left hu s
    exact ((hL (s+v) (add_pos_of_nonneg_of_pos zero_le hv)).comp hadd).sub tendsto_const_nhds
  have hX := Kyprianou.Ch04.rightContinuousTimeMeasurableV1 (fun t => X t ω) hR
  have hLm := Kyprianou.Ch04.leftLimitTimeMeasurableV1 (fun t => X t ω) (fun t => L t ω) hX hL
  rw [Kyprianou.Ch04.shiftedMarkedCountTranslationV1 X L ω hX hLm s T B hB]
  rw [← hExtract Y hYR (fun v hv => ⟨_,hYL v hv⟩)]
  apply congrArg (fun A : Set NNReal => (A.encard : ENNReal))
  ext v
  by_cases hv : 0 < v
  · haveI : (𝓝[<] v).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,hv⟩
    have hl : Function.leftLim Y v = L (s+v) ω - X s ω := leftLim_eq_of_tendsto (hYL v hv)
    have hd : Y v - Function.leftLim Y v = X (s+v) ω - L (s+v) ω := by
      rw [hl]; dsimp [Y]; ring
    have hne : (Y v ≠ Function.leftLim Y v) ↔ X (s+v) ω ≠ L (s+v) ω := by
      calc
        _ ↔ Y v - Function.leftLim Y v ≠ 0 := sub_ne_zero.symm
        _ ↔ X (s+v) ω - L (s+v) ω ≠ 0 := by rw [hd]
        _ ↔ _ := sub_ne_zero
    simp only [mem_setOf_eq, hd, sub_ne_zero, hne]
  · simp [hv]
