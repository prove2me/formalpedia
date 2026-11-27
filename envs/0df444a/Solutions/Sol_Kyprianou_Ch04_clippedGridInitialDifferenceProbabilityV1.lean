-- Prove2me | solution 1 for Kyprianou.Ch04.clippedGridInitialDifferenceProbabilityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:36:39.544329+00:00
-- url     : https://prove2.me/submissions/2e06d525-8ba2-4021-95ff-a55be11684c3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_initialCellUniformProbabilityV1
import Theorems.Thm_Kyprianou_Ch04_clippedGridZeroCellV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Restore the arbitrary bounded initial weights of two right-continuous states. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y H L : NNReal → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ w, |H 0 w| ≤ K) (hL : ∀ w, |L 0 w| ≤ K)
    (hX : ∀ t, AEMeasurable (X t) P) (hY : ∀ t, AEMeasurable (Y t) P)
    (hrX : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => X s w) (Ici t) t)
    (hrY : ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t)
    (T : NNReal) (hT : 0 < T) :
    let G := fun (Z W : NNReal → Ω → ℝ) (n : ℕ) (t : NNReal) w =>
      ∑ k ∈ Finset.range n, W (T * (k : NNReal) / (n : NNReal)) w *
        (Z (min t (T * ((k+1 : ℕ) : NNReal) / (n : NNReal))) w -
          Z (min t (T * (k : NNReal) / (n : NNReal))) w)
    let H0 := fun (s : NNReal) w => if s = 0 then 0 else H s w
    let L0 := fun (s : NNReal) w => if s = 0 then 0 else L s w
    ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (P {w | ∃ t ≤ T, δ ≤ |(G X H n t w-G X H0 n t w) -
        (G Y L n t w-G Y L0 n t w)|}).toReal ≤ η := by
  intro G H0 L0 δ hδ η hη
  let u (n : ℕ) : NNReal := T / (n : NNReal)
  have hu : Tendsto u atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat T
  have hx := Kyprianou.Ch04.initialCellUniformProbabilityV1 P X (H 0) K hK hH u hu
    hX hrX T (δ/2) (by positivity)
  have hy := Kyprianou.Ch04.initialCellUniformProbabilityV1 P Y (L 0) K hK hL u hu
    hY hrY T (δ/2) (by positivity)
  filter_upwards [hx.eventually (Iio_mem_nhds (show 0 < η/2 by positivity)),
    hy.eventually (Iio_mem_nhds (show 0 < η/2 by positivity)),
    eventually_ge_atTop (1 : ℕ)] with n hnX hnY hn
  let A : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |H 0 w * (X (min t (u n)) w-X 0 w)|}
  let B : Set Ω := {w | ∃ t ≤ T, δ/2 ≤ |L 0 w * (Y (min t (u n)) w-Y 0 w)|}
  let C : Set Ω := {w | ∃ t ≤ T, δ ≤ |(G X H n t w-G X H0 n t w) -
    (G Y L n t w-G Y L0 n t w)|}
  have hsub : C ⊆ A ∪ B := by
    rintro w ⟨t,ht,hw⟩
    let v : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    have h0 : v 0 = 0 := by simp [v]
    have hp (k : ℕ) (hk : k ∈ Finset.range n) (hk0 : k ≠ 0) : 0 < v k := by
      dsimp [v]
      positivity
    have h1 : v 1 = u n := by simp [v,u]
    have hxa := Kyprianou.Ch04.clippedGridZeroCellV1
      (fun s => X s w) (fun s => H s w) v n t (by omega) h0 hp
    have hya := Kyprianou.Ch04.clippedGridZeroCellV1
      (fun s => Y s w) (fun s => L s w) v n t (by omega) h0 hp
    change δ ≤ |(G X H n t w-G X H0 n t w)-(G Y L n t w-G Y L0 n t w)| at hw
    change G X H n t w-G X H0 n t w = _ at hxa
    change G Y L n t w-G Y L0 n t w = _ at hya
    rw [hxa,hya,h1] at hw
    by_cases h : δ/2 ≤ |H 0 w * (X (min t (u n)) w-X 0 w)|
    · exact Or.inl ⟨t,ht,h⟩
    · refine Or.inr ⟨t,ht,?_⟩
      have htri := abs_sub (H 0 w * (X (min t (u n)) w-X 0 w))
        (L 0 w * (Y (min t (u n)) w-Y 0 w))
      linarith [lt_of_not_ge h]
  have hsum : (P C).toReal ≤ (P A).toReal+(P B).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top P A) (measure_ne_top P B)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top P A,measure_ne_top P B⟩)
      ((measure_mono hsub).trans (measure_union_le A B))
  change (P A).toReal < η/2 at hnX
  change (P B).toReal < η/2 at hnY
  exact hsum.trans (by linarith)
