-- Prove2me | solution 1 for HunterPDE.Harmonic.mean_value_property
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T18:56:39.255393+00:00
-- url     : https://prove2.me/submissions/607ec613-fd6e-438f-bd17-1662a01004d8

import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_continuousOn
import Theorems.Thm_HunterPDE_Harmonic_hasDerivAt_sphereAverage_zero
import Theorems.Thm_HunterPDE_Harmonic_ball_average_eq_of_sphereAverage_eq
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Set HunterPDE.Harmonic

theorem solution {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ Ω) :
    u x = (⨍ y in Metric.ball x r, u y) ∧ u x = sphereAverage u x r := by
  have hc := (hu.mono hball).continuousOn
  have hA := sphereAverage_continuousOn hr.le hc
  have hd : ∀ t ∈ Ioc 0 r, HasDerivAt (sphereAverage u x) 0 t := by
    intro t ht
    exact hasDerivAt_sphereAverage_zero hn ht.1
      (hu.mono ((Metric.closedBall_subset_closedBall ht.2).trans hball))
  have hz : sphereAverage u x 0 = u x := by
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    letI : NeZero (volume.toSphere : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
      ⟨Measure.toSphere_ne_zero volume⟩
    simp [sphereAverage, average_const]
  have hs : ∀ t ∈ Ioc 0 r, sphereAverage u x t = u x := by
    intro t ht
    have hsub : Icc 0 t ⊆ Icc 0 r := Icc_subset_Icc le_rfl ht.2
    obtain ⟨s, hs, heq⟩ := exists_hasDerivAt_eq_slope
      (sphereAverage u x) (fun _ => 0) ht.1 (hA.mono hsub)
      (fun s hs => hd s ⟨hs.1, hs.2.le.trans ht.2⟩)
    have hdiff : sphereAverage u x t - sphereAverage u x 0 = 0 := by
      exact (div_eq_zero_iff.mp heq.symm).resolve_right (by simpa using ht.1.ne')
    rw [← hz]
    exact sub_eq_zero.mp hdiff
  exact ⟨(ball_average_eq_of_sphereAverage_eq hn hr hc hs).symm,
    (hs r ⟨hr, le_rfl⟩).symm⟩
