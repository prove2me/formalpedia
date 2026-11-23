-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiZeroStageReciprocalOccupationTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:43:44.304965+00:00
-- url     : https://prove2.me/submissions/5d335a81-d580-4d7a-a02d-e51fdde16272

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (a s : ℝ) (ha : 0 ≤ a) (has : a < s)
    (hZero : ∀ u : ℝ≥0,
      a < (u : ℝ) → (u : ℝ) < s → X u ω = 0) :
    reciprocalOccupation X (Real.toNNReal s) ω = ⊤ := by
  let f : ℝ → ℝ≥0∞ := fun u =>
    (ENNReal.ofReal (X (Real.toNNReal u) ω : ℝ))⁻¹
  have hs0 : 0 ≤ s := le_trans ha has.le
  have hsub : Set.Ioo a s ⊆ Set.Ioc (0 : ℝ) s := by
    intro u hu
    exact ⟨lt_of_le_of_lt ha hu.1, le_of_lt hu.2⟩
  have hfun : Set.EqOn f (fun _ : ℝ => (⊤ : ℝ≥0∞)) (Set.Ioo a s) := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans ha hu.1.le
    have hXu : X (Real.toNNReal u) ω = 0 := by
      apply hZero (Real.toNNReal u)
      · simpa only [Real.coe_toNNReal u hu0] using hu.1
      · simpa only [Real.coe_toNNReal u hu0] using hu.2
    simp [f, hXu]
  have hconst : (∫⁻ u in Set.Ioo a s, f u ∂volume) =
      ∫⁻ u in Set.Ioo a s, (⊤ : ℝ≥0∞) ∂volume :=
    setLIntegral_congr_fun measurableSet_Ioo hfun
  have hmeas : volume (Set.Ioo a s) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr has))
  have htop : (∫⁻ u in Set.Ioo a s, (⊤ : ℝ≥0∞) ∂volume) = ⊤ := by
    rw [setLIntegral_const, Real.volume_Ioo]
    exact ENNReal.top_mul
      (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr has)))
  have hfull : (∫⁻ u in Set.Ioc (0 : ℝ) s, f u ∂volume) = ⊤ := by
    apply top_unique
    calc
      (⊤ : ℝ≥0∞) = ∫⁻ u in Set.Ioo a s, f u ∂volume := (hconst.trans htop).symm
      _ ≤ ∫⁻ u in Set.Ioc (0 : ℝ) s, f u ∂volume :=
        lintegral_mono_set hsub
  simpa only [reciprocalOccupation, Real.coe_toNNReal s hs0, f] using hfull
