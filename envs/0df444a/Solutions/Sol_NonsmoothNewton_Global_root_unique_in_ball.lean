-- Prove2me | solution 1 for NonsmoothNewton.Global.root_unique_in_ball
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:53:49.500593+00:00
-- url     : https://prove2.me/submissions/8a6c9aa1-2d6e-4c2c-ac64-3a922b809c02

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Rademacher + Bolzano–Weierstrass: the B-limit set of a locally Lipschitz map is nonempty. -/
theorem aux_rub_bJac_nonempty {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) : ∃ V, V ∈ bJac F x := by
  obtain ⟨K, U, hU, hK⟩ := hF x
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hK' : LipschitzOnWith K F (Metric.ball x ε) := hK.mono hball
  have hae : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ Metric.ball x ε → DifferentiableWithinAt ℝ F (Metric.ball x ε) y :=
    hK'.ae_differentiableWithinAt_of_mem
  have hdense := MeasureTheory.Measure.dense_of_ae hae
  have hcl := hdense.open_subset_closure_inter (Metric.isOpen_ball (x := x) (ε := ε))
  have hx := hcl (Metric.mem_ball_self hε)
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  have hdiff : ∀ k, DifferentiableAt ℝ F (u k) := fun k =>
    ((hu k).2 (hu k).1).differentiableAt (Metric.isOpen_ball.mem_nhds (hu k).1)
  have hbd : ∀ k, fderiv ℝ F (u k) ∈ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) K := fun k => by
    rw [mem_closedBall_zero_iff]
    exact norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds (hu k).1) hK'
  obtain ⟨V, -, φ, hφ, hV⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  exact ⟨V, u ∘ φ, hlim.comp hφ.tendsto_atTop, fun k => hdiff (φ k), hV⟩

theorem aux_rub_clarke_nonempty {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) : ∃ V, V ∈ clarkeJac F x := by
  obtain ⟨V, hV⟩ := aux_rub_bJac_nonempty F hF x
  exact ⟨V, subset_convexHull ℝ _ hV⟩

end NonsmoothNewton.Global

open NonsmoothNewton.Global
open Filter Topology

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (hα : β * (γ + δ) < 1)
    (xstar ystar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ Metric.closedBall x0 r) (hystar : ystar ∈ Metric.closedBall x0 r)
    (hFx : F xstar = 0) (hFy : F ystar = 0) :
    ystar = xstar := by
  obtain ⟨V, hV⟩ := aux_rub_clarke_nonempty F hF xstar
  obtain ⟨W, -, hWV, hWn⟩ := hinv xstar hxstar V hV
  have h1 := hγ xstar hxstar ystar hystar V hV
  have h2 := hδ xstar hxstar ystar hystar
  rw [hFx, hFy, sub_zero, zero_sub, norm_neg] at h2
  set d := ystar - xstar with hd_def
  have hVd : ‖V d‖ ≤ (γ + δ) * ‖d‖ := by
    calc ‖V d‖ = ‖(V d - dirDeriv F xstar d) + dirDeriv F xstar d‖ := by rw [sub_add_cancel]
    _ ≤ ‖V d - dirDeriv F xstar d‖ + ‖dirDeriv F xstar d‖ := norm_add_le _ _
    _ ≤ γ * ‖d‖ + δ * ‖d‖ := add_le_add h1 h2
    _ = (γ + δ) * ‖d‖ := by ring
  have hβ : 0 ≤ β := le_trans (norm_nonneg _) hWn
  have hd : W (V d) = d := by
    have := congrArg (fun T => T d) hWV
    simpa using this
  have hle : ‖d‖ ≤ β * ((γ + δ) * ‖d‖) := by
    calc ‖d‖ = ‖W (V d)‖ := by rw [hd]
    _ ≤ ‖W‖ * ‖V d‖ := W.le_opNorm _
    _ ≤ β * ‖V d‖ := mul_le_mul_of_nonneg_right hWn (norm_nonneg _)
    _ ≤ β * ((γ + δ) * ‖d‖) := mul_le_mul_of_nonneg_left hVd hβ
  have hd0 : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
  have hd00 : d = 0 := norm_eq_zero.1 hd0
  exact sub_eq_zero.1 hd00
