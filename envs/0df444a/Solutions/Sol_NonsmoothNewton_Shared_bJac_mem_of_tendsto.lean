-- Prove2me | solution 1 for NonsmoothNewton.Shared.bJac_mem_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T21:51:51.604055+00:00
-- url     : https://prove2.me/submissions/7567692c-2d42-4d17-83ee-ca1299d77686

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set
open NonsmoothNewton.Shared
theorem solution {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {F : E → G} {x : E} {xseq : ℕ → E}
    {Vseq : ℕ → E →L[ℝ] G} {V : E →L[ℝ] G}
    (hx : Tendsto xseq atTop (𝓝 x))
    (hV : Tendsto Vseq atTop (𝓝 V))
    (hmem : ∀ k, Vseq k ∈ bJac F (xseq k)) :
    V ∈ bJac F x := by
  have hw := hmem
  change ∀ k, ∃ u : ℕ → E,
    Tendsto u atTop (𝓝 (xseq k)) ∧
    (∀ m, DifferentiableAt ℝ F (u m)) ∧
    Tendsto (fun m => fderiv ℝ F (u m)) atTop (𝓝 (Vseq k)) at hw
  choose u hu using hw
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos : ∀ k, 0 < ε k := by
    intro k
    dsimp [ε]
    positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0))
  have hX : ∀ k, ∃ N, ∀ m ≥ N, dist (u k m) (xseq k) < ε k := by
    intro k
    exact Metric.tendsto_atTop.mp (hu k).1 (ε k) (hεpos k)
  have hD : ∀ k, ∃ N, ∀ m ≥ N,
      dist (fderiv ℝ F (u k m)) (Vseq k) < ε k := by
    intro k
    exact Metric.tendsto_atTop.mp (hu k).2.2 (ε k) (hεpos k)
  choose NX hNX using hX
  choose ND hND using hD
  let m : ℕ → ℕ := fun k => max (NX k) (ND k)
  let z : ℕ → E := fun k => u k (m k)
  have hzX : ∀ k, dist (z k) (xseq k) ≤ ε k := by
    intro k
    exact (hNX k (m k) (le_max_left _ _)).le
  have hzD : ∀ k, dist (fderiv ℝ F (z k)) (Vseq k) ≤ ε k := by
    intro k
    exact (hND k (m k) (le_max_right _ _)).le
  have hzDiff : ∀ k, DifferentiableAt ℝ F (z k) := by
    intro k
    exact (hu k).2.1 (m k)
  have hzT : Tendsto z atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : Tendsto (fun k => ε k + dist (xseq k) x) atTop (𝓝 0) := by
      simpa only [zero_add] using
        hε0.add (tendsto_iff_dist_tendsto_zero.mp hx)
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun k => (dist_triangle (z k) (xseq k) x).trans
        (add_le_add (hzX k) le_rfl)) hb
  have hderT :
      Tendsto (fun k => fderiv ℝ F (z k)) atTop (𝓝 V) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hb :
        Tendsto (fun k => ε k + dist (Vseq k) V) atTop (𝓝 0) := by
      simpa only [zero_add] using
        hε0.add (tendsto_iff_dist_tendsto_zero.mp hV)
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun k => (dist_triangle (fderiv ℝ F (z k)) (Vseq k) V).trans
        (add_le_add (hzD k) le_rfl)) hb
  exact ⟨z, hzT, hzDiff, hderT⟩
