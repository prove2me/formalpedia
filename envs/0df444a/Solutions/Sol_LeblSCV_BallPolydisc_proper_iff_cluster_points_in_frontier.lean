-- Prove2me | solution 1 for LeblSCV.BallPolydisc.proper_iff_cluster_points_in_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:16:27.545584+00:00
-- url     : https://prove2.me/submissions/e00d6c44-2670-4c24-8258-c25315ba806d

import Mathlib
import Definitions.Def_LeblSCV_BallPolydisc_IsProperMapOn

open Filter Topology

theorem solution {n m : ℕ}
    (U : Set (Fin n → ℝ)) (V : Set (Fin m → ℝ))
    (hUo : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U)
    (hVo : IsOpen V) (hVc : IsConnected V) (hVb : Bornology.IsBounded V)
    (f : (Fin n → ℝ) → (Fin m → ℝ)) (hfUV : Set.MapsTo f U V) (hf : ContinuousOn f U) :
    LeblSCV.BallPolydisc.IsProperMapOn f U V ↔
      ∀ (p : ℕ → (Fin n → ℝ)) (x : Fin n → ℝ), (∀ k, p k ∈ U) →
        Tendsto p atTop (𝓝 x) → x ∈ frontier U →
          ∀ q : Fin m → ℝ, MapClusterPt q atTop (fun k => f (p k)) → q ∈ frontier V := by
  constructor
  · rintro ⟨-, -, hprop⟩ p x hp hpx hx q hq
    -- `q` lies in the closure of `V`
    have hqcl : q ∈ closure V := by
      rw [mem_closure_iff_clusterPt]
      exact hq.clusterPt.mono (tendsto_principal.mpr (Eventually.of_forall fun k => hfUV (hp k)))
    by_contra hqF
    -- hence `q ∈ V`
    have hqV : q ∈ V := by
      by_contra hqV
      exact hqF (by rw [hUo.frontier_eq] at hx; rw [hVo.frontier_eq]; exact ⟨hqcl, hqV⟩)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo q hqV
    -- the closed ball of radius `ε / 2` is a compact subset of `V`
    have hK : IsCompact (Metric.closedBall q (ε / 2)) := isCompact_closedBall q (ε / 2)
    have hKV : Metric.closedBall q (ε / 2) ⊆ V :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hC := hprop _ hKV hK
    obtain ⟨ψ, hψ, hψt⟩ := MapClusterPt.tendsto_subseq hq
    have hev : ∀ᶠ j in atTop, p (ψ j) ∈ U ∩ f ⁻¹' Metric.closedBall q (ε / 2) := by
      filter_upwards [hψt.eventually (Metric.closedBall_mem_nhds q (half_pos hε))] with j hj
      have hj' : f (p (ψ j)) ∈ Metric.closedBall q (ε / 2) := hj
      exact ⟨hp _, hj'⟩
    have hxC : x ∈ U ∩ f ⁻¹' Metric.closedBall q (ε / 2) :=
      hC.isClosed.mem_of_tendsto (hpx.comp hψ.tendsto_atTop) hev
    rw [hUo.frontier_eq] at hx
    exact hx.2 hxC.1
  · intro h
    refine ⟨hfUV, hf, fun K hKV hK => ?_⟩
    refine Metric.isCompact_of_isClosed_isBounded ?_ (hUb.subset Set.inter_subset_left)
    refine IsSeqClosed.isClosed ?_
    intro p x hpC hpx
    by_cases hxU : x ∈ U
    · refine ⟨hxU, ?_⟩
      have hft : Tendsto (fun k => f (p k)) atTop (𝓝 (f x)) := by
        have h1 : Tendsto f (𝓝[U] x) (𝓝 (f x)) := (hf x hxU).tendsto
        exact h1.comp (tendsto_nhdsWithin_iff.mpr ⟨hpx, Eventually.of_forall fun k => (hpC k).1⟩)
      exact hK.isClosed.mem_of_tendsto hft (Eventually.of_forall fun k => (hpC k).2)
    · exfalso
      have hxF : x ∈ frontier U := by
        rw [hUo.frontier_eq]
        exact ⟨mem_closure_of_tendsto hpx (Eventually.of_forall fun k => (hpC k).1), hxU⟩
      obtain ⟨q, hqK, φ, hφ, hφt⟩ := hK.tendsto_subseq (x := fun k => f (p k)) fun k => (hpC k).2
      have hq : MapClusterPt q atTop (fun k => f (p k)) :=
        MapClusterPt.of_comp hφ.tendsto_atTop hφt.mapClusterPt
      have hqF := h p x (fun k => (hpC k).1) hpx hxF q hq
      rw [hVo.frontier_eq] at hqF
      exact hqF.2 (hKV hqK)

#print axioms solution
