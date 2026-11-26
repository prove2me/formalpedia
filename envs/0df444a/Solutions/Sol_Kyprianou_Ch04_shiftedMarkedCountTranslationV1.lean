-- Prove2me | solution 1 for Kyprianou.Ch04.shiftedMarkedCountTranslationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:52:51.149884+00:00
-- url     : https://prove2.me/submissions/b6bfb7ea-5176-45d7-b61a-a90b582881ed

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureCountV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Translate an intrinsic marked-count window into the corresponding relative-time count. -/
theorem solution {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω)
    (hX : Measurable (fun t => X t ω)) (hL : Measurable (fun t => L t ω))
    (s T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) :
    Kyprianou.Ch04.pathJumpMeasure X L ω (Ioc (s : ℝ) ((s+T : NNReal) : ℝ) ×ˢ B) =
      ({v : NNReal | 0 < v ∧ v ≤ T ∧ X (s+v) ω ≠ L (s+v) ω ∧
        X (s+v) ω - L (s+v) ω ∈ B}).encard := by
  let S : Set NNReal := {u | 0 < u ∧ X u ω ≠ L u ω ∧
    ((u : ℝ), X u ω - L u ω) ∈ Ioc (s : ℝ) ((s+T : NNReal) : ℝ) ×ˢ B}
  let R : Set NNReal := {v | 0 < v ∧ v ≤ T ∧ X (s+v) ω ≠ L (s+v) ω ∧
    X (s+v) ω - L (s+v) ω ∈ B}
  have hSR : S = (fun v : NNReal => s+v) '' R := by
    ext u
    constructor
    · intro hu
      obtain ⟨_,hd,⟨⟨hsu,hut⟩,hb⟩⟩ := hu
      have hs : s < u := by exact_mod_cast hsu
      have ht : u ≤ s+T := by exact_mod_cast hut
      have hshift : s+(u-s) = u := add_tsub_cancel_of_le hs.le
      refine ⟨u-s, ⟨tsub_pos_iff_lt.mpr hs, ?_, ?_, ?_⟩, hshift⟩
      · simpa only [add_tsub_cancel_left] using tsub_le_tsub_right ht s
      · rwa [hshift]
      · rwa [hshift]
    · rintro ⟨v,hv,rfl⟩
      have hs : s < s+v := lt_add_of_pos_right s hv.1
      have ht : s+v ≤ s+T := by simpa only [add_comm s] using add_le_add_left hv.2.1 s
      exact ⟨lt_of_le_of_lt (show (0 : NNReal) ≤ s from zero_le) hs, hv.2.2.1,
        ⟨⟨by exact_mod_cast hs, by exact_mod_cast ht⟩,hv.2.2.2⟩⟩
  have hinj : Function.Injective (fun v : NNReal => s+v) :=
    fun a b h => add_left_cancel h
  rw [Kyprianou.Ch04.pathJumpMeasureCountV1 X L ω hX hL _ (measurableSet_Ioc.prod hB)]
  change (S.encard : ENNReal) = R.encard
  rw [hSR, hinj.encard_image R]
