-- Prove2me | solution 1 for Kyprianou.Ch04.denseBoundedPrimitiveZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:48:42.411326+00:00
-- url     : https://prove2.me/submissions/46ea01f1-ec24-4a96-bb5b-5dfc0fb59d01

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedPrimitiveClockLipschitz
open MeasureTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- A bounded primitive vanishing on a countable dense set vanishes everywhere. -/
theorem solution (g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ t : NNReal, IntegrableOn g (Icc (0:ℝ) (t:ℝ)) volume)
    (hb : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)), ‖g r‖ ≤ C)
    (hz : ∀ q : ℕ, (∫ r in Icc (0:ℝ) ((TopologicalSpace.denseSeq NNReal q : NNReal):ℝ), g r ∂volume) = 0) :
    ∀ t : NNReal, (∫ r in Icc (0:ℝ) (t:ℝ), g r ∂volume) = 0 := by
  intro t
  let A := fun u : NNReal => ∫ r in Icc (0 : ℝ) (u : ℝ), g r ∂volume
  have hLip : LipschitzWith (Real.toNNReal (C)) A := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro a b
    rw [Real.coe_toNNReal _ (hC),Real.dist_eq,NNReal.dist_eq]
    change |A a-A b| ≤ C * |(a:ℝ)-(b:ℝ)|
    rcases le_total a b with hab|hba
    · rw [abs_sub_comm (A a),abs_sub_comm (a:ℝ),abs_of_nonneg (sub_nonneg.mpr (show (a:ℝ) ≤ (b:ℝ) from hab))]
      exact boundedPrimitiveClockLipschitz _ _ (hC) hi hb a b hab
    · rw [abs_of_nonneg (sub_nonneg.mpr (show (b:ℝ) ≤ (a:ℝ) from hba))]
      exact boundedPrimitiveClockLipschitz _ _ (hC) hi hb b a hba
  have hd := TopologicalSpace.denseRange_denseSeq NNReal
  exact congrFun (hd.equalizer hLip.continuous continuous_const (funext hz)) t
