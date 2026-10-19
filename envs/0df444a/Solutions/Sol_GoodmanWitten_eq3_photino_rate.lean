-- Prove2me | solution 1 for GoodmanWitten.eq3_photino_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:50:51.380319+00:00
-- url     : https://prove2.me/submissions/29fb6486-ec12-466a-99c7-965e259a9c38

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution : ∃ C : ℝ, |C / 1.1 - 1| ≤ 0.05 ∧
    ∀ A m Q MQ lamJJ ρ v : ℝ, 0 < A → 0 < m → 0 < MQ →
      eventRatePerKgDay A (photinoCrossSection m (nucleusMass A) Q MQ lamJJ) ρ v m =
        C * (100 / MQ) ^ 4 * (4 * m * nucleusMass A / (m + nucleusMass A) ^ 2) *
          (Q / (2 / 3)) ^ 4 * lamJJ * (ρ / 1e-24) * (v / 2e7) := by
  refine ⟨6.0e26 * secondsPerDay * nucleonMass * 16 * Real.pi * fineStructure ^ 2 * hbarc ^ 2 *
      (2 / 3) ^ 4 / 1e8 * 1e-24 * 2e7 / gramsPerGeV, ?_, ?_⟩
  · have p1 := Real.pi_gt_d6
    have p2 := Real.pi_lt_d6
    unfold secondsPerDay nucleonMass fineStructure hbarc gramsPerGeV
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num), le_div_iff₀ (by norm_num)]; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num), div_le_iff₀ (by norm_num)]; nlinarith
  · intro A m Q MQ lamJJ ρ v hA hm hMQ
    unfold eventRatePerKgDay photinoCrossSection elasticCrossSection photinoAmpSq quarkChargeSq
      targetNucleiPerKg nucleusMass
    have hpi := Real.pi_pos
    have hn : 0 < nucleonMass := by unfold nucleonMass; norm_num
    have hg : 0 < gramsPerGeV := by unfold gramsPerGeV; norm_num
    have : 0 < m + A * nucleonMass := by positivity
    field_simp
    ring
