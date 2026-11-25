-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorIncrementBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:27:36.762212+00:00
-- url     : https://prove2.me/submissions/454ee2e6-1790-4c9b-b756-57df17cb4780

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorIncrementCoreV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : NNReal → Real) (d w : Real) (hd : 0 < d) (hw : 0 ≤ w)
    (hf0 : f 0 = 0)
    (hf : ∀ s t : NNReal, s ≤ t →
      f t - f s ≤ d * ((t : Real) - (s : Real))) :
    let R : NNReal → Real := fun t => max w (sSup (f '' Iic t))
    R 0 = w ∧
    (∀ t, f t ≤ R t) ∧
    (∀ s t : NNReal, s ≤ t →
      0 ≤ R t - R s ∧
      R t - R s ≤ max 0 (f s - R s + d * ((t : Real) - (s : Real)))) ∧
    LipschitzWith (Real.toNNReal d) R := by
  intro R
  obtain ⟨hz, hDom, hInc⟩ :=
    Kyprianou.Ch04.idleRegulatorIncrementCoreV1 f d w hd hw hf0 hf
  have hLip : LipschitzWith d.toNNReal R := by
    have hordered (s t : NNReal) (hst : s ≤ t) :
        dist (R s) (R t) ≤ d * dist s t := by
      have h := hInc s t hst
      have hs := hDom s
      have hst' : (s : Real) ≤ (t : Real) := hst
      have hdif := mul_nonneg hd.le (sub_nonneg.mpr hst')
      have hb : max 0 (f s - R s + d * ((t : Real) - (s : Real))) ≤
          d * ((t : Real) - (s : Real)) := max_le hdif (by linarith)
      rw [Real.dist_eq, abs_of_nonpos (by linarith [h.1]), NNReal.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hst')]
      linarith [h.2.trans hb]
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.coe_toNNReal d hd.le]
    rcases le_total s t with h | h
    · exact hordered s t h
    · rw [dist_comm (R s) (R t), dist_comm s t]
      exact hordered t s h
  exact ⟨hz, hDom, hInc, hLip⟩
