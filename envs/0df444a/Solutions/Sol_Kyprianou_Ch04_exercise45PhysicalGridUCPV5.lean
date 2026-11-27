-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalGridUCPV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:59:08.270798+00:00
-- url     : https://prove2.me/submissions/9fbfd6ed-70bb-40e4-a359-265641f9605a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45MaskedDominatedUCPV5
import Theorems.Thm_Kyprianou_Ch04_exercise45MaskedGridDifferenceV5
import Theorems.Thm_Kyprianou_Ch04_exercise45MaskedFirstCellV5
import Theorems.Thm_Kyprianou_Ch04_exercise45StoppedGridRegularV5
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Uniform pathwise convergence of the physical grid implies outer UCP despite the arbitrary weight at zero. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y H J : NNReal → Ω → ℝ)
    (hmY : ∀ t, AEMeasurable (Y t) P)
    (hmH : ∀ t, AEMeasurable (fun w => if t = 0 then 0 else H t w) P)
    (hrY : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ w, |H 0 w| ≤ K) :
    let G : (NNReal → Ω → ℝ) → ℕ → NNReal → Ω → ℝ := fun W n t w =>
      ∑ k ∈ Finset.range n, W (T * (k : NNReal) / (n : NNReal)) w *
        (Y (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
         Y (min t (T * (k : NNReal) / (n : NNReal))) w)
    (∀ᵐ w ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |G H n t w - J t w| < δ) →
    ∀ δ : ℝ, 0 < δ → Tendsto
      (fun n => (P {w | ∃ t ≤ T, δ ≤ |G H n t w - J t w|}).toReal) atTop (nhds 0) := by
  intro G hu δ hδ
  let W (t : NNReal) (w : Ω) := if t = 0 then 0 else H t w
  let A (n : ℕ) (t : NNReal) (w : Ω) := G W n (min t T) w
  let R (n : ℕ) (t : NNReal) (w : Ω) := K * |Y (min t (T / (n : NNReal))) w - Y 0 w|
  let U (n : ℕ) (t : NNReal) (w : Ω) := G H n t w - J t w
  let J' (t : NNReal) (w : Ω) := J (min t T) w
  obtain ⟨hm,hr⟩ := Kyprianou.Ch04.exercise45StoppedGridRegularV5 P Y W hmY hmH hrY T K
  have hDiff (n : ℕ) (t : NNReal) (w : Ω) : |G H n t w - G W n t w| ≤ R n t w :=
    Kyprianou.Ch04.exercise45MaskedGridDifferenceV5
      (fun s => Y s w) (fun s => H s w) T t n K hK (hb w)
  have hR : ∀ᵐ w ∂P, ∀ e : ℝ, 0 < e →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal, |R n t w| < e := by
    filter_upwards [hrY] with w hw
    exact Kyprianou.Ch04.exercise45MaskedFirstCellV5 (fun s => Y s w) T K (hw 0)
  apply Kyprianou.Ch04.exercise45MaskedDominatedUCPV5 P U A R J' T _ _ _ _ _ δ hδ
  · intro n t
    exact ⟨(hm n (min t T)).1,(hm n t).2⟩
  · filter_upwards [hr] with w hw n t
    refine ⟨?_,(hw n t).2⟩
    apply ((hw n (min t T)).1).comp (f := fun s : NNReal => min s T)
      (continuous_id.min continuous_const).continuousWithinAt
    intro s hs
    exact min_le_min (show t ≤ s from hs) le_rfl
  · filter_upwards [hu,hR] with w hw hwr
    intro L e he
    obtain ⟨N,hN⟩ := hw (e/2) (by positivity)
    obtain ⟨M,hM⟩ := hwr (e/2) (by positivity)
    refine ⟨max N M,fun n hn t ht => ?_⟩
    let s := min t T
    have h1 := hN n ((le_max_left N M).trans hn) s (min_le_right _ _)
    have h2 := hM n ((le_max_right N M).trans hn) s
    have h3 := hDiff n s w
    have h4 := abs_sub_le (G W n s w) (G H n s w) (J s w)
    rw [abs_sub_comm (G W n s w) (G H n s w)] at h4
    change |G W n s w - J s w| < e
    linarith [le_abs_self (R n s w)]
  · filter_upwards [hR] with w hw
    exact fun e he => let ⟨N,hN⟩ := hw e he; ⟨N,fun n hn t _ => hN n hn t⟩
  · filter_upwards [] with w n t ht
    have h := abs_sub_le (G H n t w) (G W n t w) (J t w)
    simp only [U,A,J',min_eq_left ht]
    calc
      _ ≤ |G H n t w - G W n t w| + |G W n t w - J t w| := h
      _ ≤ |R n t w| + |G W n t w - J t w| :=
        add_le_add ((hDiff n t w).trans (le_abs_self _)) le_rfl
      _ = _ := add_comm _ _
