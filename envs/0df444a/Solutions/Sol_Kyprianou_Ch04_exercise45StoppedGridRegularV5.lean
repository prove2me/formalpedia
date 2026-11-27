-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StoppedGridRegularV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:57:43.09488+00:00
-- url     : https://prove2.me/submissions/09c68b21-4398-4114-ab23-940fffe495e7

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Stopped deterministic grids inherit measurable sections and right-continuous paths. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y H : NNReal → Ω → ℝ)
    (hmY : ∀ t, AEMeasurable (Y t) P) (hmH : ∀ t, AEMeasurable (H t) P)
    (hrY : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (K : ℝ) :
    let G : ℕ → NNReal → Ω → ℝ := fun n t w =>
      ∑ k ∈ Finset.range n, H (T * (k : NNReal) / (n : NNReal)) w *
        (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
         Y (min t (T * (k : NNReal) / (n : NNReal))) w)
    let R : ℕ → NNReal → Ω → ℝ := fun n t w =>
      K * |Y (min t (T / (n : NNReal))) w - Y 0 w|
    (∀ n t, AEMeasurable (G n t) P ∧ AEMeasurable (R n t) P) ∧
      (∀ᵐ w ∂P, ∀ n t, ContinuousWithinAt (fun s => G n s w) (Ici t) t ∧
        ContinuousWithinAt (fun s => R n s w) (Ici t) t) := by
  intro G R
  constructor
  · intro n t
    constructor
    · change AEMeasurable (fun w => ∑ k ∈ Finset.range n, _) P
      apply Finset.aemeasurable_fun_sum
      intro k hk
      exact (hmH _).mul ((hmY _).sub (hmY _))
    · exact aemeasurable_const.mul (((hmY _).sub (hmY _)).abs)
  · filter_upwards [hrY] with w hw
    have hmin (a t : NNReal) : ContinuousWithinAt (fun s => Y (min s a) w) (Ici t) t := by
      apply (hw (min t a)).comp (f := fun s : NNReal => min s a)
        (continuous_id.min continuous_const).continuousWithinAt
      intro s hs
      exact min_le_min (show t ≤ s from hs) le_rfl
    intro n t
    constructor
    · change ContinuousWithinAt (fun s => ∑ k ∈ Finset.range n, _) (Ici t) t
      let g (k : ℕ) (s : NNReal) :=
        H (T * (k : NNReal) / (n : NNReal)) w *
          (Y (min s (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
           Y (min s (T * (k : NNReal) / (n : NNReal))) w)
      have hg (k : ℕ) : ContinuousWithinAt (g k) (Ici t) t := by
        exact continuousWithinAt_const.mul ((hmin _ _).sub (hmin _ _))
      have hsum (S : Finset ℕ) :
          ContinuousWithinAt (fun s => ∑ k ∈ S, g k s) (Ici t) t := by
        induction S using Finset.induction_on with
        | empty =>
          simpa using (continuousWithinAt_const :
            ContinuousWithinAt (fun _ : NNReal => (0 : ℝ)) (Ici t) t)
        | @insert k S hk ih =>
          simp only [Finset.sum_insert hk]
          change ContinuousWithinAt
            (g k + fun s => ∑ i ∈ S, g i s) (Ici t) t
          exact (hg k).add ih
      exact hsum (Finset.range n)
    · exact continuousWithinAt_const.mul (((hmin _ _).sub continuousWithinAt_const).abs)
