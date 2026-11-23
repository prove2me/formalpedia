-- Prove2me | solution 1 for GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:29.28685+00:00
-- url     : https://prove2.me/submissions/89b9b51c-86fd-41dd-b100-e4adf8062391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_norm_fderiv_le_of_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.SCV
theorem _root_.solution [CompleteSpace V] {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → E → V} {f : E → V} {c : E} {r : ℝ}
    (hlim : TendstoUniformlyOn F f l (ball c (2 * r)))
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) (ball c (2 * r))) :
    DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.mpr hr, differentiableOn_empty, tendstoUniformlyOn_empty]
  have hsub : ∀ x ∈ ball c r, ball x r ⊆ ball c (2 * r) := fun x hx =>
    ball_subset_ball' (by linarith [mem_ball.mp hx])
  have hC : UniformCauchySeqOn (fun n => fderiv ℂ (F n)) l (ball c r) := by
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
    have h1 := hlim.uniformCauchySeqOn _ (Metric.dist_mem_uniformity (ε := ε * r / 4) (by positivity))
    filter_upwards [h1, hF.prod_inl l, hF.prod_inr l] with m hm hm1 hm2 x hx
    apply hεu
    have hn : ball c (2 * r) ∈ 𝓝 x := mem_of_superset (ball_mem_nhds x hr) (hsub x hx)
    rw [dist_eq_norm, ← fderiv_sub (hm1.differentiableAt hn) (hm2.differentiableAt hn)]
    have := norm_fderiv_le_of_ball (f := F m.1 - F m.2) (M := ε * r / 4) hr
      ((hm1.sub hm2).mono (hsub x hx)) (fun z hz => by
        have := hm z (hsub x hx hz)
        simp only [dist_eq_norm] at this
        exact this.le)
    refine this.trans_lt ?_
    rw [div_lt_iff₀ hr]
    nlinarith [mul_pos hε hr]
  set g' : E → E →L[ℂ] V := fun x => limUnder l (fun n => fderiv ℂ (F n) x)
  have hT : TendstoUniformlyOn (fun n => fderiv ℂ (F n)) g' l (ball c r) :=
    hC.tendstoUniformlyOn_of_tendsto fun x hx => (hC.cauchy_map hx).le_nhds_lim
  have hsub' : ball c r ⊆ ball c (2 * r) := ball_subset_ball (by linarith)
  have hD : ∀ x ∈ ball c r, HasFDerivAt f (g' x) x := by
    intro x hx
    have hn : ball c r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := l) (f := F)
      (f' := fun n => fderiv ℂ (F n)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hT).mono_right
        (le_principal_iff.mpr hn)
    · filter_upwards [hF.prod_inl _, Filter.Eventually.prod_inr hn l] with p hp hp2
      exact (hp.differentiableAt (isOpen_ball.mem_nhds (hsub' hp2))).hasFDerivAt
    · filter_upwards [hn] with y hy using hlim.tendsto_at (hsub' hy)
  exact ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt,
    hT.congr_right fun x hx => (hD x hx).fderiv.symm⟩
end GlobalTheory.SCV
