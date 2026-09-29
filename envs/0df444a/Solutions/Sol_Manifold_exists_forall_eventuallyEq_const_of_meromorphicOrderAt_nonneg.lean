-- Prove2me | solution 1 for Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/85a9d75d-6830-5d0c-9af4-4fd217e9692e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg

set_option autoImplicit false

noncomputable section

open Filter Topology Set
p2m_open_scoped "Manifold P2MW.S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg.Manifold ContDiff Topology"

namespace Manifold
namespace LiouvilleRemovableProof
p2m_open "Manifold"

theorem exists_analyticAt_eventuallyEq {f : ℂ → ℂ} {c : ℂ} (hf : MeromorphicAt f c)
    (h0 : 0 ≤ meromorphicOrderAt f c) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ f =ᶠ[𝓝[≠] c] G := by
  by_cases htop : meromorphicOrderAt f c = ⊤
  · refine ⟨0, analyticAt_const, ?_⟩
    exact meromorphicOrderAt_eq_top_iff.1 htop
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    have hn0 : 0 ≤ n := by
      rw [← hn] at h0
      exact_mod_cast h0
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
    obtain ⟨G, hG, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
    refine ⟨fun z => (z - c) ^ (k : ℤ) • G z, ?_, hev⟩
    have h1 : AnalyticAt ℂ (fun z : ℂ => (z - c) ^ (k : ℤ)) c := by
      simp_rw [zpow_natCast]
      exact (analyticAt_id.sub analyticAt_const).pow k
    exact h1.smul hG

theorem eventually_eventually_of_punctured {c : ℂ} {P : ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[≠] c, P z) : ∀ᶠ z in 𝓝[≠] c, ∀ᶠ z' in 𝓝 z, P z' := by
  rw [eventually_nhdsWithin_iff] at h ⊢
  filter_upwards [h.eventually_nhds] with z hz hne
  have hne' : ∀ᶠ z' in 𝓝 z, z' ≠ c := isOpen_compl_singleton.mem_nhds hne
  filter_upwards [hz, hne'] with z' h1 h2
  exact h1 h2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

abbrev φ (x : M) : PartialEquiv M ℂ := extChartAt 𝓘(ℂ, ℂ) x

abbrev ctr (x : M) : ℂ := extChartAt 𝓘(ℂ, ℂ) x x

abbrev rd (g : M → ℂ) (x : M) : ℂ → ℂ := fun z => g ((φ x).symm z)

theorem rd_eq_comp (g : M → ℂ) {x y : M} {w : ℂ} (hw : (φ y).symm w ∈ (φ x).source) :
    rd g y w = rd g x (φ x ((φ y).symm w)) := by
  simp only [rd]
  rw [(φ x).left_inv hw]

theorem eventually_symm_mem_source {x y : M} {w : ℂ} (hw : w ∈ (φ y).target)
    (hx : (φ y).symm w ∈ (φ x).source) : ∀ᶠ w' in 𝓝 w, (φ y).symm w' ∈ (φ x).source :=
  (continuousAt_extChartAt_symm'' hw).preimage_mem_nhds (extChartAt_source_mem_nhds' hx)

variable [IsManifold 𝓘(ℂ, ℂ) ω M]

theorem analyticAt_transition (x y : M) {w : ℂ} (hw : w ∈ (φ y).target)
    (hx : (φ y).symm w ∈ (φ x).source) : AnalyticAt ℂ (φ x ∘ (φ y).symm) w := by
  have hcd := contDiffOn_ext_coord_change (I := 𝓘(ℂ, ℂ)) (n := ω) x y
  have hsrc : ((φ y).symm ≫ φ x).source ∈ 𝓝 w := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    refine Filter.inter_mem (extChartAt_target_mem_nhds' hw) ?_
    exact (continuousAt_extChartAt_symm'' hw).preimage_mem_nhds (extChartAt_source_mem_nhds' hx)
  exact (hcd.contDiffAt hsrc).analyticAt

theorem key (g : M → ℂ) (G : M → ℂ → ℂ) (hGan : ∀ x, AnalyticAt ℂ (G x) (ctr x))
    (hGeq : ∀ x, rd g x =ᶠ[𝓝[≠] (ctr x)] G x) (x : M) :
    (fun z => G ((φ x).symm z) (ctr ((φ x).symm z))) =ᶠ[𝓝 (ctr x)] G x := by

  have hoff : ∀ᶠ z in 𝓝[≠] (ctr x), G ((φ x).symm z) (ctr ((φ x).symm z)) = G x z := by
    have h1 := eventually_eventually_of_punctured (hGeq x)
    have h2 : ∀ᶠ z in 𝓝[≠] (ctr x), AnalyticAt ℂ (G x) z :=
      mem_nhdsWithin_of_mem_nhds (hGan x).eventually_analyticAt
    have h3 : ∀ᶠ z in 𝓝[≠] (ctr x), z ∈ (φ x).target :=
      mem_nhdsWithin_of_mem_nhds (extChartAt_target_mem_nhds x)
    filter_upwards [h1, h2, h3] with z hz1 hz2 hzt

    set y : M := (φ x).symm z with hy
    have hysrc : y ∈ (φ x).source := (φ x).map_target hzt
    have hτ0 : (φ x ∘ (φ y).symm) (ctr y) = z := by
      show φ x ((φ y).symm (ctr y)) = z
      rw [extChartAt_to_inv, hy, (φ x).right_inv hzt]
    have hτc : ContinuousAt (φ x ∘ (φ y).symm) (ctr y) :=
      (analyticAt_transition x y (mem_extChartAt_target y)
        (by rw [extChartAt_to_inv]; exact hysrc)).continuousAt

    have hchg : rd g y =ᶠ[𝓝 (ctr y)] (G x ∘ (φ x ∘ (φ y).symm)) := by
      have hs : ∀ᶠ w in 𝓝 (ctr y), (φ y).symm w ∈ (φ x).source :=
        eventually_symm_mem_source (mem_extChartAt_target y)
          (by rw [extChartAt_to_inv]; exact hysrc)
      have hG : ∀ᶠ w in 𝓝 (ctr y), rd g x ((φ x ∘ (φ y).symm) w) = G x ((φ x ∘ (φ y).symm) w) := by
        have : ∀ᶠ w' in 𝓝 ((φ x ∘ (φ y).symm) (ctr y)), rd g x w' = G x w' := by
          rw [hτ0]; exact hz1
        exact hτc.eventually this
      filter_upwards [hs, hG] with w hw hGw
      rw [rd_eq_comp g hw]
      exact hGw

    have hlim1 : Tendsto (rd g y) (𝓝[≠] (ctr y)) (𝓝 (G y (ctr y))) :=
      ((hGan y).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hGeq y).symm
    have hlim2 : Tendsto (rd g y) (𝓝[≠] (ctr y)) (𝓝 (G x z)) := by
      have hc : ContinuousAt (G x ∘ (φ x ∘ (φ y).symm)) (ctr y) := by
        refine ContinuousAt.comp ?_ hτc
        rw [hτ0]; exact hz2.continuousAt
      have := hc.tendsto
      rw [Function.comp_apply, hτ0] at this
      exact (this.mono_left nhdsWithin_le_nhds).congr'
        (hchg.filter_mono nhdsWithin_le_nhds).symm
    exact tendsto_nhds_unique hlim1 hlim2

  rw [Filter.EventuallyEq, ← nhdsNE_sup_pure, eventually_sup]
  refine ⟨hoff, ?_⟩
  rw [eventually_pure, extChartAt_to_inv]

omit [IsManifold 𝓘(ℂ, ℂ) ω M] in

theorem mdifferentiableAt_of_analyticAt (gt : M → ℂ) (x : M)
    (han : AnalyticAt ℂ (fun z => gt ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) gt x := by
  rw [mdifferentiableAt_iff]
  constructor
  · have hc : ContinuousAt ((fun z => gt ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) ∘ extChartAt 𝓘(ℂ, ℂ) x)
        x := han.continuousAt.comp (continuousAt_extChartAt x)
    refine hc.congr ?_
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) x] with y hy
    simp only [Function.comp_apply]
    rw [(extChartAt 𝓘(ℂ, ℂ) x).left_inv hy]
  · have : writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x gt =
        fun z => gt ((extChartAt 𝓘(ℂ, ℂ) x).symm z) := by
      ext z
      simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
        Function.comp_apply, id_eq]
    rw [this]
    exact han.differentiableAt.differentiableWithinAt

theorem main [CompactSpace M] [ConnectedSpace M] (g : M → ℂ)
    (hg : ∀ x, MeromorphicAt (rd g x) (ctr x)) (hg0 : ∀ x, 0 ≤ meromorphicOrderAt (rd g x) (ctr x)) :
    ∃ C : ℂ, ∀ x, rd g x =ᶠ[𝓝[≠] (ctr x)] fun _ => C := by
  choose G hGan hGeq using fun x => exists_analyticAt_eventuallyEq (hg x) (hg0 x)
  have hkey : ∀ x, (fun z => G ((φ x).symm z) (ctr ((φ x).symm z))) =ᶠ[𝓝 (ctr x)] G x :=
    key g G hGan hGeq
  have han : ∀ x, AnalyticAt ℂ (fun z => (fun y => G y (ctr y)) ((φ x).symm z)) (ctr x) := fun x =>
    (hGan x).congr (hkey x).symm

  have hmd : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y => G y (ctr y)) := fun x =>
    mdifferentiableAt_of_analyticAt _ x (han x)
  obtain ⟨C, hC⟩ := hmd.exists_eq_const_of_compactSpace
  refine ⟨C, fun x => ?_⟩
  have h1 : G x =ᶠ[𝓝 (ctr x)] fun _ => C := by
    filter_upwards [hkey x] with z hz
    rw [← hz]
    exact congrFun hC ((φ x).symm z)
  exact (hGeq x).trans (h1.filter_mono nhdsWithin_le_nhds)

end Manifold.LiouvilleRemovableProof

open Manifold.LiouvilleRemovableProof in

theorem solution
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (g : M → ℂ)
    (hg : ∀ x : M, MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hg0 : ∀ x : M, 0 ≤ meromorphicOrderAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x)) :
    ∃ C : ℂ, ∀ x : M, (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] fun _ => C :=
  main g hg hg0

end

end S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
end P2MW
export P2MW.S_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg (solution)
