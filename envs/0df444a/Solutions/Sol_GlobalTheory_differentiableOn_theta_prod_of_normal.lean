-- Prove2me | solution 1 for GlobalTheory.differentiableOn_theta_prod_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:53.12029+00:00
-- url     : https://prove2.me/submissions/63e4b559-91d6-48c6-a2b3-448dd0e6483a

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
import Theorems.Thm_GlobalTheory_differentiable_thetaTerm_prod
import Theorems.Thm_GlobalTheory_SCV_tendstoUniformlyOn_fderiv_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] (a b : ι → ℝ)
    {U : Set ((ι → ℂ) × (ι → ι → ℂ))} (hU : IsOpen U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ l, ∀ p ∈ K, ‖thetaTerm a b p.1 (Matrix.of p.2) l‖ ≤ u l) :
    DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) U := by
  intro c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hK : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨u, hu, hbd⟩ := hle _ hK (isCompact_closedBall c (ε / 2))
  have hr : (0 : ℝ) < ε / 4 := by positivity
  have hlim : TendstoUniformlyOn
      (fun s : Finset (ι → ℤ) => fun p : (ι → ℂ) × (ι → ι → ℂ) =>
        ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) Filter.atTop
      (Metric.ball c (2 * (ε / 4))) := by
    have h := tendstoUniformlyOn_tsum hu (fun l p hp => hbd l p hp)
    refine h.mono ?_
    intro p hp
    exact Metric.ball_subset_closedBall (by simpa [show 2 * (ε / 4) = ε / 2 by ring] using hp)
  have hF : ∀ᶠ s : Finset (ι → ℤ) in Filter.atTop, DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (Metric.ball c (2 * (ε / 4))) :=
    Filter.Eventually.of_forall fun s => by
      have h := Differentiable.sum (u := s) fun l _ => differentiable_thetaTerm_prod a b l
      have e : (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l) =
          ∑ l ∈ s, fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l := by
        funext p
        rw [Finset.sum_apply]
      rw [e]
      exact h.differentiableOn
  have hd := (GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball hlim hF).1
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt
end GlobalTheory
