-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.cyclicConstant_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-28T01:33:33.813646+00:00
-- url     : https://prove2.me/submissions/14b37f94-a75c-416f-9d33-74bcb6d4c21a

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

open HlawkaSchatten.DiagonalConstruction

theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const

theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'

theorem cyclicA_two (p : ℝ) : cyclicA p 2 = ((2 : ℝ) ^ p + 2) ^ (1 / p) := by
  simp [cyclicA]

theorem cyclicB_two (p : ℝ) : cyclicB p 2 = cyclicA p 2 := by
  rw [cyclicB, cyclicA_two]
  congr 1
  rw [show (1 : ℝ) - 2 = -1 by norm_num, abs_neg, abs_one, Real.one_rpow]
  ring

theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := by
    rw [cyclicA_two]
    exact Real.rpow_pos_of_pos (by positivity) _
  rw [cyclicRatio, cyclicB_two]
  rw [show (2 : ℝ) - 2 = 0 by norm_num, abs_zero, mul_zero, sub_zero]
  rw [show 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 by ring]
  exact div_self (by positivity)

theorem solution {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hcont : ContinuousOn (cyclicRatio p) (Set.Icc (1 / 2 : ℝ) 2) :=
    (continuousOn_cyclicRatio hp).mono (fun t ht => by
      simp only [Set.mem_Ici]; linarith [ht.1])
  have hcomp : IsCompact (cyclicRatio p '' Set.Icc (1 / 2 : ℝ) 2) :=
    isCompact_Icc.image_of_continuousOn hcont
  rw [cyclicConstant]
  refine le_csSup hcomp.bddAbove ⟨2, ?_, cyclicRatio_two p⟩
  constructor <;> norm_num
