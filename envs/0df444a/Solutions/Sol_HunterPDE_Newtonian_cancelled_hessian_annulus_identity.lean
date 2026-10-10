-- Prove2me | solution 1 for HunterPDE.Newtonian.cancelled_hessian_annulus_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:58:18.981993+00:00
-- url     : https://prove2.me/submissions/46748c81-b050-4ae0-baec-a31136deb564
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MeasureTheory_mixed_green_identity_annulus
import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Ring
open MeasureTheory HunterPDE.Newtonian Filter
open scoped ContDiff Topology

theorem solution (n : ℕ) (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) (R r : ℝ) (hR : 0 < R)
    (hr : 0 < r) (hrR : r < R) (hsupp : tsupport f ⊆ Metric.ball x R) (i j : Fin n) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      secondPartial (fundamentalSolution n) i j (x - y) * (f y - f x)) =
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      fundamentalSolution n (x - y) * secondPartial f i j y)
    + f x * (R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere))
    + r ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        fundamentalSolution n (-(r • w.1)) * partialDeriv f j (x + r • w.1) * w.1 i
        + partialDeriv (fundamentalSolution n) i (-(r • w.1)) *
          (f (x + r • w.1) - f x) * w.1 j ∂volume.toSphere) := by
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => f y - f x
  have hg : ContDiff ℝ 2 g := hf.sub contDiff_const
  have h := MeasureTheory.mixed_green_identity_annulus n (by omega)
    (fundamentalSolution n) (fundamentalSolution_partial n hn).1 g hg x R r hR hr hrR i j
  have hd : partialDeriv g j = partialDeriv f j := by
    funext y
    simp [g, partialDeriv, fderiv_sub_const]
  have hdd : secondPartial g i j = secondPartial f i j := by
    unfold secondPartial
    rw [hd]
  have hb (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      x + R • w.1 ∉ tsupport f := by
    intro hw
    have hmem := hsupp hw
    have hwN : ‖w.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using w.property
    have hdist : dist (x + R • w.1) x = R := by
      simp [dist_eq_norm, norm_smul, hwN, Real.norm_eq_abs, abs_of_pos hR]
    rw [Metric.mem_ball, hdist] at hmem
    exact (lt_irrefl R) hmem
  have hv (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      f (x + R • w.1) = 0 := image_eq_zero_of_notMem_tsupport (hb w)
  have hp (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      partialDeriv f j (x + R • w.1) = 0 := by
    simp [partialDeriv, fderiv_of_notMem_tsupport ℝ (hb w)]
  rw [hdd, hd] at h
  have ho :
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        fundamentalSolution n (-(R • w.1)) * partialDeriv f j (x + R • w.1) * w.1 i
        + partialDeriv (fundamentalSolution n) i (-(R • w.1)) * g (x + R • w.1) * w.1 j
        ∂volume.toSphere) =
      -f x * (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        partialDeriv (fundamentalSolution n) i (-(R • w.1)) * w.1 j ∂volume.toSphere) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [g, hv w, hp w]
    ring
  rw [ho] at h
  dsimp only [g] at h
  convert h using 1 <;> ring
