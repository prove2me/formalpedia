-- Prove2me | solution 1 for HunterPDE.Harmonic.mean_value_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T14:27:19.332993+00:00
-- url     : https://prove2.me/submissions/8d990d4e-ef16-4f50-a219-23052d78ac74

import Definitions.Def_HunterPDE_Harmonic_Subharmonic
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_mono_of_laplacian_nonneg
import Theorems.Thm_HunterPDE_Harmonic_ball_average_ge_of_sphereAverage_ge

open MeasureTheory Set HunterPDE.Harmonic
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ Ω) :
    (IsSubharmonicOn Ω u →
        u x ≤ (⨍ y in Metric.ball x r, u y) ∧ u x ≤ sphereAverage u x r) ∧
      (IsSuperharmonicOn Ω u →
        (⨍ y in Metric.ball x r, u y) ≤ u x ∧ sphereAverage u x r ≤ u x) := by
  have lower : ∀ v : EuclideanSpace ℝ (Fin n) → ℝ, IsSubharmonicOn Ω v →
      v x ≤ (⨍ y in Metric.ball x r, v y) ∧ v x ≤ sphereAverage v x r := by
    intro v hv
    have hvC : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 2 v y :=
      fun y hy => hv.1.contDiffAt (hΩ.mem_nhds (hball hy))
    have hmono := sphereAverage_mono_of_laplacian_nonneg hn hr hvC
      (fun y hy => hv.2 y (hball (Metric.ball_subset_closedBall hy)))
    have hz : sphereAverage v x 0 = v x := by
      let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      let : NeZero (volume.toSphere : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
        ⟨Measure.toSphere_ne_zero volume⟩
      simp [sphereAverage, average_const]
    have hs : ∀ t ∈ Ioc 0 r, v x ≤ sphereAverage v x t := by
      intro t ht
      rw [← hz]
      exact hmono ⟨le_rfl, hr.le⟩ ⟨ht.1.le, ht.2⟩ ht.1.le
    exact ⟨ball_average_ge_of_sphereAverage_ge hn hr
      (hv.1.continuousOn.mono hball) hs, hs r ⟨hr, le_rfl⟩⟩
  constructor
  · exact lower u
  · intro hu
    have hnsub : IsSubharmonicOn Ω (-u) := by
      refine ⟨hu.1.neg, ?_⟩
      intro y hy
      simpa only [InnerProductSpace.laplacian_neg, Pi.neg_apply, neg_nonneg] using hu.2 y hy
    obtain ⟨hb, hs⟩ := lower (-u) hnsub
    simpa only [Pi.neg_apply, sphereAverage, average_neg, neg_le_neg_iff] using And.intro hb hs
