-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_capped_renewal_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:22:08.437558+00:00
-- url     : https://prove2.me/submissions/4de9e36b-3d13-4d29-9478-bb9a11479331

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_passage_split
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- On the capped finite-passage event the original infimum reward is the product of the stopped and future rewards. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) =
      min (Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w) (n : WithTop NNReal))
    (hB : ∀ᵐ w ∂P, BddBelow (range (fun t : NNReal => L.X t w)))
    (β : ℝ) (hβ : 0 ≤ β) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≤ (n : WithTop NNReal)}
    let W : Ω → ℝ≥0∞ := A.indicator (fun w => ENNReal.ofReal (Real.exp (β * L.X (T w) w)))
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    (∫⁻ w, A.indicator (fun z => R (fun t => L.X t z)) w ∂P) =
      (∫⁻ w, W w * R (fun t => L.X (T w + t) w - L.X (T w) w) ∂P) := by
  intro A W R
  apply lintegral_congr_ae
  filter_upwards [hB] with w hw
  by_cases hA : w ∈ A
  · have hle : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≤ (n : WithTop NNReal) := hA
    have ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (T w : WithTop NNReal) :=
      ((hT w).trans (min_eq_left hle)).symm
    have H := Kyprianou.Ch04.cor412_dyadic_passage_split L w (T w) ht hw β hβ
    simp only [W,Set.indicator_of_mem hA]
    exact H
  · simp [W,hA]
