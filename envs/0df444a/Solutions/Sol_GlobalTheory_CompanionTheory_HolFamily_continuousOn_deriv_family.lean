-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolFamily.continuousOn_deriv_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:32.66563+00:00
-- url     : https://prove2.me/submissions/53a77d50-d192-4ab9-a9c0-c6c1042ac62c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily
namespace GlobalTheory.CompanionTheory.HolFamily
theorem _root_.solution (P : Type) [TopologicalSpace P] (U : Set ℂ) (hU : IsOpen U)
    (H : P → ℂ → ℂ) (hc : ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U))
    (hd : ∀ p, DifferentiableOn ℂ (H p) U) :
    ContinuousOn (fun q : P × ℂ => deriv (H q.1) q.2) (Set.univ ×ˢ U) := by
  rintro ⟨p0, z0⟩ ⟨-, hz0⟩
  simp only at hz0
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hU z0 hz0
  have hR : 0 < e / 3 := by positivity
  set R := e / 3 with hRdef
  have hKU : Metric.closedBall z0 (2 * R) ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    rw [hRdef]; linarith
  let K : Set ℂ := Metric.closedBall z0 (2 * R)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall z0 (2 * R))
  have hFc : Continuous (fun x : P × K => H x.1 x.2) := by
    have : Continuous (fun x : P × K => ((x.1, (x.2 : ℂ)) : P × ℂ)) := by fun_prop
    exact hc.comp_continuous this (fun x => ⟨Set.mem_univ _, hKU x.2.2⟩)
  let F : C(P × K, ℂ) := ⟨fun x => H x.1 x.2, hFc⟩
  let G : C(P, C(K, ℂ)) := F.curry
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hGc : Tendsto G (𝓝 p0) (𝓝 (G p0)) := G.continuous.tendsto p0
  have h1 : ∀ᶠ p in 𝓝 p0, dist (G p) (G p0) < ε / 2 * R / 2 :=
    (Metric.tendsto_nhds.1 hGc) _ (by positivity)
  have hdc : ContinuousAt (deriv (H p0)) z0 :=
    ((hd p0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have h2 : ∀ᶠ z in 𝓝 z0, dist (deriv (H p0) z) (deriv (H p0) z0) < ε / 2 :=
    (Metric.tendsto_nhds.1 hdc) _ (by positivity)
  have h3 : ∀ᶠ z in 𝓝 z0, z ∈ Metric.ball z0 R := Metric.ball_mem_nhds z0 hR
  have h4 := h1.prod_nhds (h2.and h3)
  filter_upwards [nhdsWithin_le_nhds h4]
  rintro ⟨p, z⟩ ⟨hp, hz, hzR⟩
  simp only at hp hz hzR ⊢
  have hsub : Metric.closedBall z R ⊆ K := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    rw [Metric.mem_ball] at hzR
    have := dist_triangle w z z0
    linarith
  have hfd : DifferentiableOn ℂ (fun w => H p w - H p0 w) U := (hd p).sub (hd p0)
  have hzU : z ∈ U := hKU (hsub (Metric.mem_closedBall_self hR.le))
  have hnh : U ∈ 𝓝 z := hU.mem_nhds hzU
  have hderiv : deriv (fun w => H p w - H p0 w) z = deriv (H p) z - deriv (H p0) z :=
    deriv_fun_sub ((hd p).differentiableAt hnh) ((hd p0).differentiableAt hnh)
  have hbound : ∀ w ∈ Metric.sphere z R, ‖H p w - H p0 w‖ ≤ ε / 2 * R / 2 := by
    intro w hw
    have hwK : w ∈ K := hsub (Metric.sphere_subset_closedBall hw)
    have := ContinuousMap.dist_apply_le_dist (f := G p) (g := G p0) (⟨w, hwK⟩ : K)
    have h5 : dist (G p ⟨w, hwK⟩) (G p0 ⟨w, hwK⟩) = ‖H p w - H p0 w‖ := by
      rw [dist_eq_norm]; rfl
    rw [← h5]
    exact this.trans hp.le
  have hcauchy : ‖deriv (fun w => H p w - H p0 w) z‖ ≤ ε / 2 * R / 2 / R :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      (hfd.diffContOnCl_ball (hsub.trans hKU)) hbound
  have hval : ε / 2 * R / 2 / R = ε / 4 := by field_simp; ring
  rw [hval, hderiv] at hcauchy
  calc dist (deriv (H p) z) (deriv (H p0) z0)
      ≤ dist (deriv (H p) z) (deriv (H p0) z) + dist (deriv (H p0) z) (deriv (H p0) z0) :=
        dist_triangle _ _ _
    _ < ε := by
        rw [dist_eq_norm (deriv (H p) z)]
        linarith
end GlobalTheory.CompanionTheory.HolFamily
