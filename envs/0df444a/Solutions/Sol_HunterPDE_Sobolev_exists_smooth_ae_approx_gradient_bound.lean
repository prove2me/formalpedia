-- Prove2me | solution 1 for HunterPDE.Sobolev.exists_smooth_ae_approx_gradient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T17:36:58.051175+00:00
-- url     : https://prove2.me/submissions/b6067625-1df0-43ec-a65a-efa96fb51b1e

import Theorems.Thm_HunterPDE_Sobolev_eLpNorm_gradient_convolution_le
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ENNReal NNReal Convolution

theorem solution {n : ℕ} (hn : 1 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧
        MemLp g (ENNReal.ofReal p) volume)
    (C : ℝ≥0)
    (hC : eLpNorm (HunterPDE.Shared.weakGradNorm Set.univ f) (ENNReal.ofReal p) volume ≤
      (C : ℝ≥0∞)) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v j)) ∧
      (∀ j, eLpNorm (fun z => ‖gradient (v j) z‖) (ENNReal.ofReal p) volume ≤
        (C : ℝ≥0∞)) ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => v j x) atTop (𝓝 (f x)) := by
  classical
  obtain ⟨d, hd, _⟩ := hf ⟨0, hn⟩
  have hloc : LocallyIntegrable f volume := locallyIntegrableOn_univ.mp hd.1
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun j =>
    { rIn := (1 / ((j : ℝ) + 1)) / 2
      rOut := 1 / ((j : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun j =>
    (φ j).normed volume ⋆[lsmul ℝ ℝ, volume] f
  refine ⟨v, ?_, ?_, ?_⟩
  · intro j
    exact (φ j).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ j).contDiff_normed hloc
  · intro j
    apply le_trans (HunterPDE.Sobolev.eLpNorm_gradient_convolution_le
      (by simpa using (ENNReal.ofReal_le_ofReal hp)) ENNReal.ofReal_ne_top f hloc hf
      ((φ j).normed volume) ?_ (φ j).nonneg_normed (φ j).integral_normed) hC
    exact ⟨(φ j).contDiff_normed, (φ j).hasCompactSupport_normed, Set.subset_univ _⟩
  · exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ
      (Filter.Eventually.of_forall (fun j => show (φ j).rOut ≤ 2 * (φ j).rIn by
        dsimp [φ]
        linarith)) hloc
