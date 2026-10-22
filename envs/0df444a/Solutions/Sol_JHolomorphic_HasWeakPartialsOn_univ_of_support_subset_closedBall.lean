-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.univ_of_support_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:16:29.587995+00:00
-- url     : https://prove2.me/submissions/125710e8-4b5e-40e6-9146-28c54e9196bf

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct



namespace JHolomorphic

open MeasureTheory Metric Filter
open scoped ContDiff Topology

theorem HasWeakPartialsOn.univ_of_support_subset_closedBall_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set ℂ} {c : ℂ} {R R' : ℝ} (hR : 0 < R)
    (hRR' : R < R') (hU : closedBall c R' ⊆ U) {f fs ft : ℂ → E}
    (h : HasWeakPartialsOn U f fs ft) (hf : Function.support f ⊆ closedBall c R)
    (hfs : Function.support fs ⊆ closedBall c R) (hft : Function.support ft ⊆ closedBall c R) :
    HasWeakPartialsOn Set.univ f fs ft := by
  intro φ hφ hφc _
  let ψ : ContDiffBump c := ⟨(R + R') / 2, R', by linarith, by linarith⟩
  set φ' : ℂ → ℝ := fun z => ψ z * φ z with hφ'
  have hφ'd : ContDiff ℝ ∞ φ' := ψ.contDiff.mul hφ
  have hφ'c : HasCompactSupport φ' := ψ.hasCompactSupport.mul_right
  have hφ'U : tsupport φ' ⊆ U := (tsupport_mul_subset_left).trans (by
    rw [ψ.tsupport_eq]; exact hU)
  obtain ⟨h1, h2⟩ := h φ' hφ'd hφ'c hφ'U
  -- near the closed ball of radius `R`, `φ'` agrees with `φ`
  have hloc : ∀ z ∈ ball c ((R + R') / 2), φ' =ᶠ[𝓝 z] φ := by
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    simp only [hφ', ψ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  have hR2 : closedBall c R ⊆ ball c ((R + R') / 2) :=
    closedBall_subset_ball (by linarith)
  have key : ∀ (g : ℂ → E), Function.support g ⊆ closedBall c R → ∀ v : ℂ,
      (fun z => fderiv ℝ φ' z v • g z) = (fun z => fderiv ℝ φ z v • g z) ∧
      (fun z => φ' z • g z) = (fun z => φ z • g z) := by
    intro g hg v
    constructor <;> funext z
    · by_cases hz : z ∈ ball c ((R + R') / 2)
      · rw [(hloc z hz).fderiv_eq]
      · have : g z = 0 := Function.notMem_support.1 (fun h' => hz (hR2 (hg h')))
        simp [this]
    · by_cases hz : z ∈ ball c ((R + R') / 2)
      · rw [(hloc z hz).eq_of_nhds]
      · have : g z = 0 := Function.notMem_support.1 (fun h' => hz (hR2 (hg h')))
        simp [this]
  rw [(key f hf 1).1, (key fs hfs 1).2] at h1
  rw [(key f hf Complex.I).1, (key ft hft 1).2] at h2
  exact ⟨h1, h2⟩

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set ℂ} {c : ℂ} {R R' : ℝ} (hR : 0 < R)
    (hRR' : R < R') (hU : closedBall c R' ⊆ U) {f fs ft : ℂ → E}
    (h : HasWeakPartialsOn U f fs ft) (hf : Function.support f ⊆ closedBall c R)
    (hfs : Function.support fs ⊆ closedBall c R) (hft : Function.support ft ⊆ closedBall c R) :
    HasWeakPartialsOn Set.univ f fs ft :=
  HasWeakPartialsOn.univ_of_support_subset_closedBall_aux hR hRR' hU h hf hfs hft
