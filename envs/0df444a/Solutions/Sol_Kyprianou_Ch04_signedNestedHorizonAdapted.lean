-- Prove2me | solution 1 for Kyprianou.Ch04.signedNestedHorizonAdapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:17:41.731474+00:00
-- url     : https://prove2.me/submissions/34f2a54e-9d40-4acf-a9f8-70e28ecdd203

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_jointNestedNonnegIntegralsMeasurable
open MeasureTheory Filter Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact nested signed compensator measurability follows from the past cutoff. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (k : ℝ → ℝ → Omega → ℝ) (t : NNReal)
    (hm : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) :
    StronglyMeasurable[F t] (fun w => ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫ x, k s x w ∂nu ∂volume) := by
  let V := volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))
  letI : MeasurableSpace Omega := F t
  let f := fun z : Omega × (ℝ × ℝ) =>
    if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0
  have h := (jointNestedNonnegIntegralsMeasurable V nu f hm).2
  have he (w : Omega) :
      (∫ s, ∫ x, f (w,(s,x)) ∂nu ∂V) =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, k s x w ∂nu ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [f,if_pos hs])
  simpa only [he] using h.stronglyMeasurable
