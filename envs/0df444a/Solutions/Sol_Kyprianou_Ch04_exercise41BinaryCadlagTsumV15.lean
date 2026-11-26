-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BinaryCadlagTsumV15
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:13:28.984138+00:00
-- url     : https://prove2.me/submissions/b287ce92-4818-422a-8f57-88c5e59c98bb

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41BinaryCadlagFlatV15
import Theorems.Thm_Kyprianou_Ch04_exercise41BinaryCadlagFiniteV15
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite_jump_drift_deficit_telescope
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open AvramDividend.Classical
open Kyprianou.Ch04
theorem solution
    (f : NNReal → ℝ) (h0 : f 0 = 0)
    (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (hLVal : ∀ u, 0 < u → Function.leftLim f u = 0 ∨ Function.leftLim f u = -1)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (T : NNReal) :
    Set.Finite (Function.support (fun u : Ioc (0 : NNReal) T =>
      f u - Function.leftLim f u)) ∧
    f T = ∑' u : Ioc (0 : NNReal) T, (f u - Function.leftLim f u) := by
  have hfin := exercise41BinaryCadlagFiniteV15 f hVal hLVal hR hL T
  have hs : Set.Finite (Function.support (fun u : Ioc (0 : NNReal) T =>
      f u - Function.leftLim f u)) := by
    apply (Set.Finite.preimage Subtype.val_injective.injOn hfin).subset
    intro u hu
    exact ⟨u.2.1,u.2.2,hu⟩
  refine ⟨hs,?_⟩
  have hflat (s t : NNReal) (hst : s ≤ t) (_ : t ≤ T)
      (hj : ∀ u ∈ Ioc s t, f u - Function.leftLim f u = 0) :
      (t : ℝ) * 0 - f t = (s : ℝ) * 0 - f s := by
    rw [exercise41BinaryCadlagFlatV15 f hVal hR hL s t hst hj]
    simp
  have H := avram_bv_finite_jump_drift_deficit_telescope f 0 T h0 hfin hflat
  simp only [mul_zero,zero_sub] at H
  have he : (∑' u : Ioc (0 : NNReal) T, (Function.leftLim f u - f u)) =
      ∑' u : NNReal, if 0 < u ∧ u ≤ T then Function.leftLim f u - f u else 0 := by
    rw [tsum_subtype (Ioc (0 : NNReal) T) (fun u => Function.leftLim f u - f u)]
    simp only [Set.indicator_apply,Set.mem_Ioc]
  have H' : (∑' u : Ioc (0 : NNReal) T, (-(f u - Function.leftLim f u))) = -f T := by
    simpa only [neg_sub,he] using H
  rw [tsum_neg] at H'
  linarith
